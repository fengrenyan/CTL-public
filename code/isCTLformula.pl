

:- module(isCTLformula, [is_CTLformula/1]).






%decide whether an experssion is a CTL formula.
is_CTLformula(P) :- atom(P).
is_CTLformula(-P) :- is_CTLformula(P).
is_CTLformula(P & Q) :- is_CTLformula(P), is_CTLformula(Q).
is_CTLformula(P \/ Q) :- is_CTLformula(P), is_CTLformula(Q).%/
is_CTLformula(P -> Q) :- is_CTLformula(P), is_CTLformula(Q).
is_CTLformula(^(@P)) :- is_CTLformula(P).
is_CTLformula(^(P $ Q)) :- is_CTLformula(P), is_CTLformula(Q).
is_CTLformula(^(*P)) :- is_CTLformula(P).
is_CTLformula(^(?P)) :- is_CTLformula(P).
is_CTLformula(~(@P)) :- is_CTLformula(P).
is_CTLformula(~(P $ Q)) :- is_CTLformula(P), is_CTLformula(Q).
is_CTLformula(~(*P)) :- is_CTLformula(P).
is_CTLformula(~(?P)) :- is_CTLformula(P).

