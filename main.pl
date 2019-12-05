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
    
solve(Goal, Database) :- writeln(Database), writeln(Goal).

:- 
    phrase_from_file(start(X), 'file.txt'),
    create_database(X, Database),
    write('pulog> '),
    read(Goal),
    solve(Goal, Database),
    halt.