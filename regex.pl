complement_regex_string(Regex_String, Regex_Comp_String) :-
  string_codes(Regex_String, Regex_Codes),
  parse_regex(Regex_Codes, Regex),
  regex_nfa(Regex, NFA),
  nfa_dfa(NFA, DFA),
  dfa_complement(DFA, DFA_Comp),
  dfa_regex(DFA_Comp, Regex_Comp),
  show_regex(Regex_Comp, Regex_Comp_Codes),
  string_codes(Regex_Comp_String, Regex_Comp_Codes).
parse_regex(RS, R) -->
  "0", parse_regex([regex_char(0)|RS], R);
  "1", parse_regex([regex_char(1)|RS], R);
  "_", parse_regex([regex_empty|RS], R);
  "!", parse_regex([regex_null|RS], R).
parse_regex([R0,R1|RS], R) -->
  "|", parse_regex([regex_union(R1, R0)|RS], R);
  ";", parse_regex([regex_concat(R1, R0)|RS], R).
parse_regex([R0|RS], R) -->
  "+", parse_regex([regex_concat(R0, regex_kleene(R0))|RS], R).
parse_regex([R],R) --> \+ [_].
parse_regex(S, R) :-
  parse_regex([], R, S, []).
fresh(S), [T] -->
  [S], {T is S + 1}.
is_nfa(nfa{states: _, initial: _, final: _, delta: DS}) :-
  forall(member(D, DS), is_delta(D)).

is_delta(__From-__Char-__To).
regex_nfa(regex_empty, NFA) -->
  fresh(A),
  {NFA = nfa{states: [A], initial: A, final: A, delta: []}}.
regex_nfa(regex_null, NFA) -->
  fresh(A), fresh(B),
  {NFA = nfa{states: [A, B], initial: A, final: B, delta: []}}.
regex_nfa(regex_char(C), NFA) -->
  fresh(A), fresh(B),
  {NFA = nfa{states: [A, B], initial: A, final: B, delta: [A-C-B]}}.
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
regex_nfa(Regex, NFA) :-
  regex_nfa(Regex, NFA, [0], _).
nfa_dfa(NFA, DFA) :-
  DFA = dfa{states: States, initial: I, final: F, delta: Delta},
  setof(S, epsilon_close(NFA.delta, NFA.initial, S), I),
  new_states([I], NFA.delta, States),
  findall(S, (member(S, States), member(NFA.final, S)), F),
  bagof(D, S^(member(S, States), new_transition(S, NFA.delta, D)), Delta).
epsilon_close(_,S,S).
epsilon_close(Delta, S, E) :-
  select(S-e-T, Delta, Delta2),
  findall(E,(member(E,Delta2), E=_-e-S), Del),
  subtract(Delta2, Del, Delta3),
  epsilon_close(Delta3, T, E).
new_transition(States, Delta, States-D-TS) :-
  member(D, [0, 1]),
  % TODO: this doesn't handle multiple transistions on the same character out
  % of a single state. Need to add a union somewhere.
  (setof(S, T^F^(
    member(F,States),
    member(F-D-T, Delta),
    epsilon_close(Delta, T, S)
  ), TS) -> true ; TS=[]).
new_states(States, Delta, AllStates) :-
  setof(E, S^(member(S, States), new_state(S, Delta, E)), Expanded),
  subtract(Expanded, States, New), (
    New = [], AllStates = States;
    New = [_|_], union(States, New, Union), new_states(Union, Delta, AllStates)
  ).

new_state(States, Delta, New) :-
  new_transition(States, Delta, _-_-New).
dfa_complement(DFA, Complement) :-
  Complement = dfa{
    states: DFA.states,
    initial: DFA.initial,
    delta: DFA.delta,
    final: Final
  },
  subtract(DFA.states, DFA.final, Final).
:- table dfa_regex/5.

dfa_regex(DFA, -1, I, J, Simpl_RE) :-
  nth0(I, DFA.states, QI),
  nth0(J, DFA.states, QJ),
  setof(R, C^(
    member(C, [0, 1]),
    (member(QI-C-QJ, DFA.delta) ->
      R = regex_char(C);
      R = regex_null)
  ), RES),
  (I = J ->
    fold_union([regex_empty|RES], RE);
    fold_union(RES, RE)),
  simpl_regex(RE,Simpl_RE).

dfa_regex(DFA, K, I, J, RE) :-
  K > -1,
  Pred_K is K - 1,
  dfa_regex(DFA, Pred_K, I, K, R_IK),
  dfa_regex(DFA, Pred_K, K, K, R_KK),
  dfa_regex(DFA, Pred_K, K, J, R_KJ),
  dfa_regex(DFA, Pred_K, I, J, R_IJ),
  simpl_regex(regex_union(regex_concat(R_IK, regex_concat(regex_kleene(R_KK), R_KJ)), R_IJ), RE).
dfa_regex(DFA, Regex) :-
  length(DFA.states, L), K is L - 1,
  nth0(I, DFA.states, DFA.initial),
  findall(Regex_F, (
    member(Final, DFA.final),
    nth0(J, DFA.states, Final),
    dfa_regex(DFA, K, I, J, Regex_F)
  ), Regex_List),
  fold_union(Regex_List, Regex).

fold_union(Regex_List, Union) :-
  foldl([V0, E, V1]>>(V1=regex_union(V0, E)), Regex_List, regex_null, Union).
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
show_regex(regex_char(0), `0`).
show_regex(regex_char(1), `1`).
show_regex(regex_empty, `_`).
show_regex(regex_null, `!`).
show_regex(regex_union(L,R), S) :-
  show_regex(L, SL),
  show_regex(R, SR),
  append([SL, SR, `|`], S).
show_regex(regex_concat(L,R), S) :-
  show_regex(L, SL),
  show_regex(R, SR),
  append([SL, SR, `;`], S).
show_regex(regex_kleene(K), S) :-
  show_regex(K, SK),
  append(SK, `*`, S).
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