start(X) --> predicates_and_facts(X).

predicates_and_facts([H]) --> predicate_or_fact(H).
predicates_and_facts([H|T]) --> 
    predicate_or_fact(H), predicates_and_facts(T).

predicate_or_fact(p(name(Name), params(Params), body(Predicates))) --> 
    predicate_call(Name, Params), ":-", predicates_call(Predicates).
predicate_or_fact(f(name(Name), params(Params))) --> 
    predicate_call(Name, Params), ".".

predicate_call(Name, Params) --> lower_chars(Name), "(", parameters(Params), ")".

predicates_call([pred_call(Name, Params)|T]) --> predicate_call(Name, Params), ",", predicates_call(T).
predicates_call([pred_call(Name, Params)|_]) --> predicate_call(Name, Params), ".".

parameters([P|T]) --> parameter(P), ",", parameters(T).
parameters([P|_]) --> parameter(P).
parameter(a(P)) --> lower_chars(P).
parameter(t(P)) --> term_name(P).

lower_chars([C|T]) -->
    lower_char(C), !,
    lower_chars(T).
lower_chars([]) -->
    [].
lower_char(C) -->
    [C],    
    { char_type(C, lower)
    }.
term_name([C|T]) --> upper_char(C), !, lower_chars(T). 
upper_char(C) -->
    [C],
    { char_type(C, upper)
    }.

digits([D|T]) -->
    digit(D), !,
    digits(T).
digits([]) -->
    [].

digit(D) -->
    [D],
    { code_type(D, digit)
    }.

solve(_, X) :- writeln(X).

:- 
    phrase_from_file(start(X), 'file.txt'),
    write('pulog> '),
    read(I),
    solve(I, X),
    halt.