%The  Removingatoms  process

:- module(removeAtom, [removeAtom/3]).


removeAtom([],_, []).
removeAtom([C|L], V, R):- C = snf_clause(Type, H, T, I), 
	(intersection(H, V, []),!, obtainAtom(T, T1), (intersection(T1, V,[]), C1=C; C1=[]);
		C1=[]
	), removeAtom(L, V, R1),
	(C1=[], R=R1; append([C1], R1, R)).
	