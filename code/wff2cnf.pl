
:- module(wff2cnf, [dnf2wff/2, cnf2wff/2, wff2cnf/2, wff2dnf/2]).


:- op(500,fx,-).
%:- op(500,fx,~).
:- op(780,xfy,&).
:- op(790,xfy,\/).%/
:- op(800,xfy,->).
:- op(800,xfy,<->).


/* dnf2wff(L,W) convert a DNF list to a formula */

dnf2wff([],false) :- !.
dnf2wff([[]],true) :- !.
dnf2wff([L], W) :- list2conjunct(L,W), !.
dnf2wff([L1|L2], W1 \/ W2) :- list2conjunct(L1, W1), dnf2wff(L2,W2).

/* cnf2wff(L,W) convert a CNF list to a formula */

cnf2wff([[]],false) :- !.
cnf2wff([],true) :- !.
cnf2wff([L], W) :- list2disjunct(L,W), !.
cnf2wff([L1|L2], W1 & W2) :- list2disjunct(L1, W1), cnf2wff(L2,W2).


/* list2conjunct(L,A): A is the conjunction of all formulas in L */

list2conjunct([P],P) :- !.
list2conjunct([P | L],P & W) :- list2conjunct(L,W).


/* list2disjunct(L,A): A is the disjunction of all formulas in L: A=false when
   L is empty */

list2disjunct(L, true) :- member(true,L), !.
list2disjunct(L, true) :- member(-P,L), member(P,L), !.
list2disjunct(L, W) :- sort(L,L1), delete(L1,false,L2), list2disj(L2,W), !.
list2disj([], false) :- !.
list2disj([P],P) :- !.
list2disj([P | L],P \/ W) :- list2disj(L,W).%/


/* wff2dnf transforms a wff to its disjunctive normal form in list format */

wff2dnf(P,[[P]]) :- prop(P), !.
wff2dnf(-P,[[-P]]) :- prop(P), !.
wff2dnf(P->Q, L) :- wff2dnf(-P\/Q, L).%/
wff2dnf(P<->Q, L) :- wff2dnf((P->Q)&(Q->P), L).
wff2dnf(P\/Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2), append(L1,L2,L).%/
wff2dnf(P&Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2),
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L).
wff2dnf(-P, L) :- wff2cnf(P,L1), negate(L1,L).


/* negate(L1,L): negate L1 in DNF (CNF) and make it into a CNF (DNF). */
negate([],[]) :- !.
negate([[]],[[]]) :- !.
negate(L1,L) :- bagof(X, Y^(member(Y, L1), negate_one_clause(Y,X)), L).

/* negate_one_clause(L1, L2): make all elements in L1 into its complement */
negate_one_clause(L1, L2) :- bagof(X, Y^(member(Y,L1), complement(Y,X)), L2).



%----------wff2cnf------and--------wff2dnf--------
wff2cnf(P, [[P]]) :- prop(P), !.
wff2cnf(-P, [[-P]]) :- prop(P), !.
wff2cnf(P->Q, L) :- wff2cnf(-P\/Q, L), !.%/
wff2cnf(P<->Q, L) :- wff2cnf((-P\/Q)&(-Q\/P), L), !.%/
wff2cnf(P&Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), append(L1,L2,L), !.
wff2cnf(P\/Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), %/
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L), !.
wff2cnf(-P, L) :- wff2dnf(P, L1), negate(L1, L), !.

/* wff2cnf(W,NewW) :- negation_inside(W,W1), wff2cnf0(W1,NewW).
*/
wff2cnf0(P, [[P]]) :- prop(P), !.
wff2cnf0(-P, [[-P]]) :- prop(P), !.
wff2cnf0(P&Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), union(L1,L2,L), !.
wff2cnf0(P\/Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), %/
    setof(X, Y^Z^(member(Y,L1), member(Z,L2), union(Y,Z,X)), L), !.
	
complement(true,false) :- !.
complement(false,true) :- !.
complement(P,-P) :- prop(P).
complement(-P,P) :- prop(P).