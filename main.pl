start(X) --> predicates_and_facts(X).

predicates_and_facts([H]) --> predicate_or_fact(H).
predicates_and_facts([H|T]) --> 
    predicate_or_fact(H), predicates_and_facts(T).

predicate_or_fact(p(name(Name), params(Params), body(Predicates))) --> 
    predicate_call(Name, Params), ":-", predicates_call(Predicates).
predicate_or_fact(f(name(Name), params(Params))) --> 
    predicate_call(Name, Params), ".".

predicate_call(Name, Params) --> chars(Name), "(", parameters(Params), ")".

predicates_call([pred_call(Name, Params)|T]) --> predicate_call(Name, Params), ",", predicates_call(T).
predicates_call([pred_call(Name, Params)|_]) --> predicate_call(Name, Params), ".".

parameters([P|T]) --> parameter(P), ",", parameters(T).
parameters([P|_]) --> parameter(P).
parameters([pred_call(Name, Params)|T]) --> predicate_call(Name, Params), ",", parameters(T).
parameters([pred_call(Name, Params)|_]) --> predicate_call(Name, Params).
parameter(P) --> chars(P).

chars([C|T]) -->
    char(C), !,
    chars(T).
chars([]) -->
    [].
char(C) -->
    [C],    
    { char_type(C, alnum)
    }.

create_functor(Name, Params, Functor) :-
    atom_codes(AtomName, Name),
    length(Params, Length),
    functor(Functor, AtomName, Length),
    pass_args(Functor, Params, 1).

pass_args(_, [], _).
pass_args(Functor, [pred_call(Name, Params)|T], N) :-
    create_functor(Name, Params, Arg),
    arg(N, Functor, Arg),
    N1 is N + 1,
    pass_args(Functor, T, N1).
pass_args(Functor, [H|T], N) :-
    atom_codes(Arg, H),
    arg(N, Functor, Arg),
    N1 is N + 1,
    pass_args(Functor, T, N1).

pred_call2functor([], []).
pred_call2functor([pred_call(Name, Params)|T], [Functor|TD]) :-
    create_functor(Name, Params, Functor),
    pred_call2functor(T, TD).

create_database([], []).
create_database([f(name(Name), params(Params))|T], [f(Functor)|TD]) :-
    create_functor(Name, Params, Functor),
    create_database(T, TD).
create_database([p(name(Name), params(Params), body(Predicates))|T], [p(Functor, PredCallFunctors)|TD]) :- 
    create_functor(Name, Params, Functor),
    pred_call2functor(Predicates, PredCallFunctors),
    create_database(T, TD).
    
search_db(Goal, [f(H)|T], [f(H)|Tl]) :-
    functor(Goal, Name, ArgsCount),
    functor(H, Name, ArgsCount),
    search_db(Goal, T, Tl).
search_db(Goal, [p(L, R)|T], [p(L, R)|Tl]) :-
    functor(Goal, Name, ArgsCount),
    functor(L, Name, ArgsCount),
    search_db(Goal, T, Tl).
search_db(Goal, [_|T], R) :-
    search_db(Goal, T, R).
search_db(_, [], []).

is_same_args(T1, T2) :-
    functor(T1, _, ArgsCount),
    is_same_args(T1, T2, ArgsCount, 0).
is_same_args(T1, T2, ArgsCount, N) :-
    N < ArgsCount,
    N1 is N + 1,
    arg(N1, T1, A),
    arg(N1, T2, A),
    is_same_args(T1, T2, ArgsCount, N1).
is_same_args(_, _, N, N).

uny(X, Y) :- var(X), var(Y), X = Y.
uny(X, Y) :- var(X), nonvar(Y), X = Y.
uny(X, Y) :- var(Y), nonvar(X), Y = X.
uny(X, Y) :- nonvar(X), nonvar(Y), atomic(X), atomic(Y), X = Y.
uny(X, Y) :- nonvar(X), nonvar(Y), compound(X), compound(Y), uny_term(X, Y).

uny_term(X, Y) :- functor(X, F, N), functor(Y, F, N), mgu_parallel(X, Y, N).
mgu_parallel(T1, T2, N) :- numlist(1, N, L), concurrent_maplist(uny_arg(T1, T2), L).
uny_arg(X, Y, N) :- arg(N, X, ArgX), arg(N, Y, ArgY), uny(ArgX, ArgY).


parse_candidates(Goal, _, [f(H)|_]) :-
    uny(Goal, H).
parse_candidates(Goal, Database, [p(L, R)|_]) :-
    uny(Goal, L),
    solves(R, Database).
parse_candidates(Goal, Database, [_|T]) :-
    parse_candidates(Goal, Database, T).
parse_candidates(_, _, []) :- fail.

solves([H|T], Database) :-
    solve(H, Database),
    solves(T, Database).
solves([], _).

solve(Goal, Database) :- 
    writeln(Goal), 
    writeln(Database),
    search_db(Goal, Database, Candidates),
    writeln(Candidates),
    parse_candidates(Goal, Database, Candidates).

?- 
    phrase_from_file(start(X), 'tmp'),
    create_database(X, Database),
    write('pulog> '),
    read(Goal),
    solve(Goal, Database),
    writeln(Goal),
    halt.