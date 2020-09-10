%model checking in CNF

modelCheck(V, CNF) :- sat(V, CNF, R),
	(R=false, write("\n------------------\n"),
	write(V), write(" is not a model of "), write(CNF),
	write("\n------------------\n"), !;
	write("\n------------------\n"),
	write(V), write(" is a model of "), write(CNF),
	write("\n------------------\n")).

sat(V, [], []).
sat(V, [H|CNF], R) :- sat_clause(V, H, R1), 
	(R1 = false, R= R1;  sat(V, CNF, R)).
	
	
	
sat_clause(V, C, C1) :- intersection(V, C, R1), negation(C, C1), intersection(V, C1, R2), 
	(R1 =[], (not(R2=[]), C1=false, !; C1=[], !); C1=[], !).
	%(R1=[], (R2=[], !; false, !); !).



negation([],[]).
negation([H|T], [H1|T1]) :- 
	(H = - X, H1 = X; H1 = - H), 
	negation(T, T1).