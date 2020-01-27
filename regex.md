---
title: Complementing Regular Expressions
author: John Kastner
---

# Introduction

In this program we attempt to complete the ["Complement of a Regex"][1]
question posted to Code Golf & Coding Challenges using Prolog. Briefly, the
challenge is to take as input a simplified postfix regular expression (regex)
dialect defined  over the alphabet $\{0,1\}$ and output a new regex that
matches exactly those strings that were not matched by the original regex.

The approach we will use is as follows:

1. Parse the string representation of regex into an abstract syntax tree.
2. Convert the abstract syntax tree of the regex into a non-deterministic
   finite automaton (NFA).
3. Convert the NFA into a deterministic finite automaton (DFA).
4. Complement the DFA. This is accomplished by complementing the set of
   accepting states.
5. Convert the resulting DFA into a regular expression.

# Parsing Regular Expressions

We first need to construct an abstract syntax tree for a simplified regex. This
is easy using Prologs built in syntax for DCGs. We define a predicate
`parse_regex//2` where the first argument is the current stack of encountered
regex and the second is the final regex constructed by the parse.

The simplest cases are the single character regex . If we see `0` of `1`, we
construct a regex for a character literal and push it onto the stack. Matching
`_` for the empty regex and `!` for the null regex is handled similarly.

```{.prolog file=regex.pl}
parse_regex(RS, R) -->
  "0", parse_regex([regex_char(0)|RS], R);
  "1", parse_regex([regex_char(1)|RS], R);
  "_", parse_regex([regex_empty|RS], R);
  "!", parse_regex([regex_null|RS], R).
```

Handling concatenation and union regex is more complicated because they are
constructed from previously encountered regex . In both cases, there must be at
least two regex on the stack. If they are present and `|` is encountered, the
regex are popped and their union is push back onto the stack before continuing
the parse. If `;` is encountered, their concatenation is pushed instead.

```{.prolog file=regex.pl}
parse_regex([R0,R1|RS], R) -->
  "|", parse_regex([regex_union(R1, R0)|RS], R);
  ";", parse_regex([regex_concat(R1, R0)|RS], R).
```

Parsing the `+` quantifier a very similar but, it only requires one regular
expression on the stack. The regex pushed onto the stack in this case is more
interesting because we do not include `+` as a regex combinator. It is instead
defined as the concatenation of a regex with the Kleene closure for the same
expression (i.e. `RR*`).

```{.prolog file=regex.pl}
parse_regex([R0|RS], R) -->
  "+", parse_regex([regex_concat(R0, regex_kleene(R0))|RS], R).
```

The final step in parsing is handling the end of the input string. When there
are no more characters available, we examine the stack to determine if there if
it contains a single regex . When this is the case, that expression the final
parsed expression. If there is more than one regular expression on the stack,
then the input string was not a well formed postfix regex , so the predicate
fails.

```{.prolog file=regex.pl}
parse_regex([R],R) --> \+ [_].
```

With the DCG defined, we can define and additional predicate `parse_regex/2`
that invokes the DCG predicate with an initially empty stack and requiring that
the entire input string is consumed while parsing.

```{.prolog file=regex.pl}
parse_regex(S, R) :-
  parse_regex([], R, S, []).
```

# Converting Regular Expressions to NFA

```{.prolog file=regex.pl}
fresh(S), [T] -->
  [S], {T is S + 1}.

regex_nfa(regex_char(C), NFA) -->
  fresh(A), fresh(B),
  {NFA = nfa{states: [A, B], initial: A, final: B, delta: [A-C-B]}}.

regex_nfa(regex_empty, NFA) -->
  fresh(A),
  {NFA = nfa{states: [A], initial: A, final: A, delta: []}}.

regex_nfa(regex_null, NFA) -->
  fresh(A), fresh(B),
  {NFA = nfa{states: [A], initial: A, final: B, delta: []}}.

regex_nfa(regex_union(L, R), NFA) -->
  regex_nfa(L, NFA_L),
  regex_nfa(R, NFA_R),
  fresh(I), fresh(F),
  {append([NFA_L.states, NFA_R.states, [I, F]], States),
   Delta_I = [I-e-NFA_L.initial, I-e-NFA_R.initial],
   Delta_F = [NFA_L.final-e-F, NFA_R.final-e-F],
   append([Delta_F, Delta_I, NFA_L.delta, NFA_R.delta], Delta),
   NFA = nfa{states: States, initial: I, final: F, delta: Delta}}.

regex_nfa(regex_concat(L, R), NFA) -->
  regex_nfa(L, NFA_L),
  regex_nfa(R, NFA_R),
  {append(NFA_L.states, NFA_R.states, States),
   Delta_M = [NFA_L.final-e-NFA_R.initial],
   append([Delta_M, NFA_L.delta, NFA_R.delta], Delta),
   I = NFA_L.initial, F = NFA_R.final,
   NFA = nfa{states: States, initial: I, final: F, delta: Delta}}.

regex_nfa(regex_kleene(K), NFA) -->
  regex_nfa(K, NFA_K),
  {Delta_K = [NFA_K.initial-e-NFA_K.final, NFA_K.final-e-NFA_K.initial],
   append(Delta_K, NFA_K.delta, Delta),
   I = NFA_K.initial, F = NFA_K.final,
   NFA = nfa{states: NFA_K.states, initial: I, final: F, delta: Delta}}.
```

# Converting NFA to DFA

```{.prolog file=regex.pl}

epsilon_close(_,S,S).
epsilon_close(Delta, S, E) :-
  select(S-e-T, Delta, Delta2),

  % Not stricly required, but this eliminates
  % duplicate results
  findall(E,(member(E,Delta2), E=_-e-S), Del),
  subtract(Delta2, Del, Delta3),

  epsilon_close(Delta3, T, E).

new_transition(States, Delta, States-D-TS) :-
  member(D, [0, 1]),
  setof(S, T^F^(member(F,States), member(F-D-T, Delta), epsilon_close(Delta, T, S)), TS).

expand_state(State, Delta, NewState) :-
  member(D, [0, 1]),
  setof(E, S^N^(member(S, State), member(S-D-N, Delta), epsilon_close(Delta, N, E)), NewState).

new_states(States, Delta, AllStates) :-
  setof(E, S^(member(S, States), expand_state(S, Delta, E)), Expanded),
  subtract(Expanded, States, New), (
    New = [], AllStates = States;
    New = [_|_], union(States, New, Union), new_states(Union, Delta, AllStates)
  ).

nfa_dfa(NFA, DFA) :-
  DFA = dfa{states: States, initial: I, final: F, delta: Delta},
  setof(S, epsilon_close(NFA.delta, NFA.initial, S), I),
  new_states([I], NFA.delta, States),
  bagof(D, S^(member(S, States), new_transition(S, NFA.delta, D)), Delta),
  bagof(S, (member(S, States), member(NFA.final, S)), F).
```

# Complementing DFA

# Converting DFA to Regular Expressions

# Appendix: Graphiz Output

```{.prolog file=regex.pl}
term_codes(T, C) :-
  term_string(T, TS),
  string_codes(TS, C).

graphviz_delta(F-D-T, G) :-
  term_codes(F, FC),
  term_codes(T, TC),
  term_codes(D, DC),
  append([`"`,FC, `" -> "`, TC, `" [ label="`,DC,`"];\n`], G).

graphviz_finals(F, FS) :-
  (is_list(F), !, FL = F;
   FL = [F]),
   maplist(graphviz_final, FL, FSS), append(FSS, FS).

graphviz_final(F, FS) :-
  term_codes(F, FC),
  append([`"`, FC, `" [shape=doublecircle];\n`], FS).

graphviz_initial(I, IS) :-
  term_codes(I, IC),
  append([`"`, IC, `" [shape=diamond];\n`], IS).

graphviz(NFA, G) :-
  maplist(graphviz_delta, NFA.delta, GS),
  graphviz_finals(NFA.final, FS),
  graphviz_initial(NFA.initial, IS),
  append([[`digraph {\n`, FS, `\n`, IS], GS, [`}\n`]], GSS),
  append(GSS, G).

graphviz_file(NFA, Out) :-
  graphviz(NFA, G),
  open(Out, write, Stream),
  string_codes(GS, G),
  write(Stream, GS),
  close(Stream).

:- use_module(library(process)).

graphviz_display(NFA) :-
  graphviz(NFA, G),
  string_codes(GS, G),

  tmp_file_stream(text, Dot_File, Dot_Stream),
  write(Dot_Stream, GS),
  close(Dot_Stream),

  tmp_file_stream(binary, PNG_File, PNG_Stream),
  close(PNG_Stream),
  process_create(path(dot), ['-Tpng', '-o', PNG_File, Dot_File], []),

  process_create(path(display), [PNG_File], []),

  delete_file(Dot_File),
  delete_file(PNG_File).
```

[1]: https://codegolf.stackexchange.com/questions/161108/complement-of-a-regex
