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

We now need to transform the abstract syntax tree of regular expression into a
NFA which can be done using [Thompson's construction][2]. While we do not use
the exact same construction, the intuition is identical. 

Before implementing the construction, we need a way to obtain unique
identifiers for states in the NFA. We can do this by assigning the first state
to be `0` and incrementing the identifier for each subsequent state. In an
imperative language, the current value of the identifier might be tracked in a
global variable or local variable outside the body of a loop. A global variable
could be used in Prolog, but it is not desirable. Instead, we can opt for an
approach similar what would be used in the functional paradigm: a function
takes as part of its input the current identifier value, and returns with its
output and additional value for the next available identifier. The problem with
this approach is that we explicitly thread some state though the program. To
avoid this overhead, something similar to the state monad in Haskell can be
used.

In Prolog, the state monad is approximated using a DCG. The current identifier
value is tracked as the first and only element of the list being processed.
When an identifier is needed, the value is removed from the list, incremented,
and added back onto the list. The original value can then be used as an
identifier. The DCG predicate `fresh//1` handles the list updates and unifies
its argument with the available identifier value.

```{.prolog file=regex.pl}
fresh(S), [T] -->
  [S], {T is S + 1}.
```

To implement the construction, we also need some data structure to represent
an NFA. Recall that an NFA is [defined by a 5-tuple][3]
$(Q, \Sigma, \Delta, q_0, f)$: a set of states, an alphabet, a transition
function, and initial state, and a final state. We are working with a fixed
alphabet ($\{0,1\}$), so we will ignore $\Sigma$ and encode the remaining four
elements in a dictionary defined as follows. Note that the transition function
is defined by a set of triples rather than a function.

```{.prolog file=regex.pl}
is_nfa(nfa{states: _, initial: _, final: _, delta: DS}) :-
  forall(member(D, DS), is_delta(D)).

is_delta(__From-__Char-__To).
```

The two simplest regular expressions are the empty regular expression and the
null regular expression. NFA constructed for the empty regular expression is
an NFA with exactly one state that is both the initial and the final state
(no transitions are required). An identifier for this state is obtained by
unifying `A` in `fresh//1`.

```{.prolog file=regex.pl}
regex_nfa(regex_empty, NFA) -->
  fresh(A),
  {NFA = nfa{states: [A], initial: A, final: A, delta: []}}.
```

The null regex does not accept any strings, so there should be not way to move
from the initial state to the final state. This is encoded by obtaining two
state identifiers for the initial and final state while not generating any
transitions between them.

```{.prolog file=regex.pl}
regex_nfa(regex_null, NFA) -->
  fresh(A), fresh(B),
  {NFA = nfa{states: [A, B], initial: A, final: B, delta: []}}.
```

A character literal regex follows very directly from this. Instead of there
being no path from `A` to `B`, there should be single path that requires
transitioning on the character in question.

```{.prolog file=regex.pl}
regex_nfa(regex_char(C), NFA) -->
  fresh(A), fresh(B),
  {NFA = nfa{states: [A, B], initial: A, final: B, delta: [A-C-B]}}.
```

The following three cases are somewhat more complicate since they require
integrating one or more existing NFA into a new NFA. In all cases we first
obtain NFA for the sub-expressions for the input regular expression with 
recursive calls to `regex_nfa//2`.

To construct the NFA for a union of two regular expression, we need to
construct the union of the sub-expressions NFA. To do this, we first obtain
two fresh states for the resulting NFA: one for the initial state (`I`) and one
for the final state (`F`). Transitions are then required between the new states
and the existing NFA. From the initial state, there must be a transitions on
the empty string ($\varepsilon$, written here as `e`) to the initial state
of both NFA. From the final state of both NFA, there must be a transitions on
$\varepsilon$ to the new final state. The states and transitions for the final
NFA are the union of these new states and transitions with all existing states
and transitions from both NFA.

```{.prolog file=regex.pl}
regex_nfa(regex_union(L, R), NFA) -->
  fresh(I),
  regex_nfa(L, NFA_L),
  regex_nfa(R, NFA_R),
  fresh(F),
  {append([NFA_L.states, NFA_R.states, [I, F]], States),
   Delta_I = [I-e-NFA_L.initial, I-e-NFA_R.initial],
   Delta_F = [NFA_L.final-e-F, NFA_R.final-e-F],
   append([Delta_F, Delta_I, NFA_L.delta, NFA_R.delta], Delta),
   NFA = nfa{states: States, initial: I, final: F, delta: Delta}}.
```

For a concatenation, we do not need any new states. The new initial state is
the initial state of the left NFA while the new final states is the final state
of the right NFA. A transitions on $\varepsilon$ is then required between the
final state of the left NFA and the initial state of the right NFA.

```{.prolog file=regex.pl}
regex_nfa(regex_concat(L, R), NFA) -->
  regex_nfa(L, NFA_L),
  regex_nfa(R, NFA_R),
  {append(NFA_L.states, NFA_R.states, States),
   Delta_M = [NFA_L.final-e-NFA_R.initial],
   append([Delta_M, NFA_L.delta, NFA_R.delta], Delta),
   I = NFA_L.initial, F = NFA_R.final,
   NFA = nfa{states: States, initial: I, final: F, delta: Delta}}.
```

As in the previews cases, constructing the NFA for a Kleene closure requires
first constructing the NFA for a sub-expression. Since a Kleene closure can
satisfy the regex once, the initial and final states of this NFA should not be
changed. We will add transitions so that the expression can be satisfied more
than one time or zero times. Satisfying the expression zero times is the same
as skipping over the recursively constructed NFA entirely. We encode this
possibility by adding a transition on $\varepsilon$ from the initial state to
the final state. To satisfy the expression more than once, we should be able to
return to the state initial state after reaching the final state. This is
encoded by an $\varepsilon$ transition from the final state to the initial
state.

```{.prolog file=regex.pl}
regex_nfa(regex_kleene(K), NFA) -->
  regex_nfa(K, NFA_K),
  {Delta_K = [NFA_K.initial-e-NFA_K.final, NFA_K.final-e-NFA_K.initial],
   append(Delta_K, NFA_K.delta, Delta),
   I = NFA_K.initial, F = NFA_K.final,
   NFA = nfa{states: NFA_K.states, initial: I, final: F, delta: Delta}}.
```

# Converting NFA to DFA

We use the usual [powerset construction][4] to convert NFA to DFA. The exact
implementation is modified to only construct reachable states.

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
  (setof(S, T^F^(
    member(F,States),
    member(F-D-T, Delta),
    epsilon_close(Delta, T, S)
  ), TS) -> true ; TS=[]).

new_state(States, Delta, New) :-
  new_transition(States, Delta, _-_-New).

new_states(States, Delta, AllStates) :-
  setof(E, S^(member(S, States), new_state(S, Delta, E)), Expanded),
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

```{.prolog file=regex.pl}
dfa_complement(DFA, Complement) :-
  Complement = dfa{
    states: DFA.states,
    initial: DFA.initial,
    delta: DFA.delta,
    final: Final
  },
  subtract(DFA.states, DFA.final, Final).
```

# Converting DFA to Regular Expressions

We convert a complemented DFA into a regular expression using 
[Kleene's Algorithm][5].

```{.prolog file=regex.pl}

dfa_regex(DFA, -1, I, J, RE) :-
  (I = J ->
    Base = regex_empty;
    Base = regex_null),
  nth0(I, DFA.states, QI),
  nth0(J, DFA.states, QJ),
  setof(R, C^(
    member(C, [0, 1]),
    (member(QI-C-QJ, DFA.delta) ->
      R = regex_char(C);
      R = regex_null)
  ), RES),
  foldl([V0, E, V1]>>(V1=regex_union(V0, E)), RES, Base, RE).

dfa_regex(DFA, K, I, J, regex_union(regex_concat(R_IK, regex_concat(regex_kleene(R_KK), R_KJ)), R_IJ)) :-
  K > -1,
  Pred_K is K - 1,
  dfa_regex(DFA, Pred_K, I, K, R_IK),
  dfa_regex(DFA, Pred_K, K, K, R_KK),
  dfa_regex(DFA, Pred_K, K, J, R_KJ),
  dfa_regex(DFA, Pred_K, I, J, R_IJ).


simpl_regex(regex_union(A,B), C) :-
  simpl_regex(A, C),
  simpl_regex(B, C),!.
simpl_regex(regex_concat(E,A), B) :-
  simpl_regex(E, regex_empty),
  simpl_regex(A, B),!.
simpl_regex(regex_concat(A,E), B) :-
  simpl_regex(E, regex_empty),
  simpl_regex(A, B),!.
simpl_regex(regex_union(A,N), B) :-
  simpl_regex(N, regex_null),
  simpl_regex(A,B),!.
simpl_regex(regex_union(N,A), B) :-
  simpl_regex(N, regex_null),
  simpl_regex(A,B),!.
simpl_regex(regex_concat(_,N), regex_null) :-
  simpl_regex(N, regex_null),!.
simpl_regex(regex_concat(N,_), regex_null) :-
  simpl_regex(N, regex_null),!.
simpl_regex(regex_kleene(E), regex_empty) :-
  simpl_regex(E, regex_empty),!.
simpl_regex(regex_kleene(N), regex_null) :-
  simpl_regex(N, regex_null),!.
simpl_regex(regex_kleene(K), regex_kleene(L)) :-
  simpl_regex(K, L).
simpl_regex(regex_concat(A,B), regex_concat(C,D)) :-
  simpl_regex(A,C),
  simpl_regex(B,D).
simpl_regex(regex_union(A,B), regex_union(C,D)) :-
  simpl_regex(A,C),
  simpl_regex(B,D).
simpl_regex(regex_null, regex_null).
simpl_regex(regex_empty, regex_empty).
simpl_regex(regex_char(C), regex_char(C)).
```

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
  append([`initial [label="", shape=none, height=.0,width=.0];\n`,
         `initial -> "`, IC, `";`], IS).

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
[2]: https://en.wikipedia.org/wiki/Thompson%27s_construction
[3]: https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton#Formal_definition
[4]: https://en.wikipedia.org/wiki/Powerset_construction
[5]: https://en.wikipedia.org/wiki/Kleene%27s_algorithm
