% The mortgage program of Example 2.1 of the 1997 report (Fairtlough, Mendler
% and Walton), clause for clause the program `CLPExamples.mortgage` of the Lean
% library, run under SWI-Prolog's library(clpq) (Holzbaur's CLP(Q)).
%
%   swipl scripts/clp-compare/mortgage.pl D REPS
%
% runs  once(mortgage(P, D, 1/100, 172165/100, 0))  REPS times in one
% process, after one untimed warm-up run, and prints one JSON line: the
% wall-clock time of each repetition (get_time/1, seconds), their median, and
% the value of P (a rational).  Startup and the loading of clpq are not timed.

:- use_module(library(clpq)).

mortgage(P, D, I, MP, B) :- {D =< 1, B + MP = P*(I+1)}.
mortgage(P, D, I, MP, B) :- {1 < D}, mortgage(P*(I+1) - MP, D - 1, I, MP, B).

one(D, T, P) :-
    get_time(T0),
    once(mortgage(P, D, 1/100, 172165/100, 0)),
    get_time(T1),
    T is T1 - T0.

median(Ts, M) :-
    msort(Ts, S), length(S, N), K is N // 2, nth0(K, S, M).

main :-
    current_prolog_flag(argv, [DA, RA|_]),
    atom_number(DA, D), atom_number(RA, Reps),
    one(D, _, P0),
    findall(T, (between(1, Reps, _), one(D, T, _)), Ts),
    median(Ts, M),
    format("{\"system\": \"swipl-clpq\", \"D\": ~w, \"reps\": ~w, \"median_s\": ~6f, \"times_s\": ~w, \"P\": \"~w\"}~n",
           [D, Reps, M, Ts, P0]).

:- initialization(main, main).
