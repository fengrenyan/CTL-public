
:- module(tranCTL2SNF, [tran2SNFCl/2, tran2SNF/5]).






%tran2SNFCl(F, V1, L): transform a CTL formula into a set of snf clauses
tran2SNFCl([], []).
tran2SNFCl([H|L],R) :- tranH2C(H, C), tran2SNFCl(L, R1), append([C], R1, R).

tranH2C(start -> P, C) :- prop(P), C = start_clause([start], [P]).
tranH2C(Q -> P, C) :- is_dis(P), negation([Q], Q1),  wff2cnf(P, P1), P1 = [P2], append(Q1, P2, P3), C = true_clause([true], P3).
tranH2C([Q -> ^(*P),I], C) :- wff2cnf(P, P1), P1 = [P2], C = exist_next_clause([Q], P2, I).
tranH2C([Q -> ^(?P),I], C) :- wff2cnf(P, P1), P1 = [P2], C = exist_future_clause([Q], P2, I).
tranH2C(Q -> ~(*P), C) :- wff2cnf(P, P1), P1 = [P2], C = global_next_clause([Q], P2).
tranH2C(Q -> ~(?P), C) :- wff2cnf(P, P1), P1 = [P2], C = global_future_clause([Q], P2).


tran2SNF([], Ind, N, V, []) :- V=[].
tran2SNF(L, Ind, N, V, R) :- tran2SNF_list(L, V1, Ind, N, IndM, NM, L1),  %Ind表示index的初始值0，IndM表示index的最大值（结束transform过程后的值）； N表示变量的初始值0，NM表示transform结束后引入的原子的个数-1.
	(L1 = L, R = L1, V = V1;
		tran2SNF(L1, IndM, NM, V2, R), append(V1, V2, V)).

tran2SNF_list([], V, Ind, N, Ind, N, []) :- V=[].
tran2SNF_list([H|T], V1, Ind, N, IndM, NM, L) :- transF(H, Ind, V2, N, IndM1, NM1, L1), 
	tran2SNF_list(T, V3, IndM1, NM1, IndM, NM, L3), append(V2, V3, V1), append(L1, L3, L4), sort(L4, L).
	

%transF(start -> P, Ind, V, Ind, IndM, IndM, C) :-  C = start_clause([start], [P]).
%transF(Q -> P, Ind, V, Ind, IndM, IndM, C) :- is_dis(P), negation([Q], Q1),  wff2cnf(P, P1), P1 = [P2], append(Q1, P2, P3), %C = true_clause([true], P3).
transF(Q -> (P1 & P2), Ind, V, N, IndM, NM, L) :- NM = N, IndM=Ind, L = [Q -> P1, Q -> P2], V=[].
transF(Q -> (P1 \/ P2), Ind, V, N, IndM, NM, L) :-  IndM=Ind,%/ 
	(is_dis(P1), !, L1=[], N1=N, V2=[];
		(N1 is N +1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), V2=[Y1], L1=(Y1 -> P1))
	),
	(is_dis(P2), !, N2=N1, NM=N1, V3=[], L2=[];
		(N2 is N1 +1, NM=N2, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L1=[], (L2=[], L =[Q -> (P1 \/ P2)], V = [];  %/
				L = [L2, Q -> P1 \/ Y2], V = [Y2]); %/
		(L2 =[], L = [L1, Q -> Y1 \/P2], V = [Y1];  %/
			L = [L1, L2, Q -> Y1 \/ Y2], V =[Y1, Y2] %/
		)
	).
	
	
/*transF(Q -> ^(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind+1,
	(is_lit(P1), !, L1=[], N1=N, V2=[];
		(N1 is N +1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), V2=[Y1], L1=(Y1 -> P1))
	),
	(is_lit(P2), !, N2=N1, V3=[], L2=[];
		(N2 is N1 +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L1=[], (L2=[], tran2U(Q -> ^(P1 $ P2), N, IndM, Vx, L), V = [Vx], NM is N +1;  
					tran2U(Q -> ^(P1 $ Y2), N2, IndM, Vx, R1), append([L2], R1, L), V = [Y2, Vx], NM is N2 +1); 
		(L2 =[], tran2U(Q -> ^(Y1 $ P2), N2, IndM, Vx, R2), append([L1], R2, L), V = [Y1, Vx], NM is N + 1;
			 NM is N2 + 1, string_concat('x', NM, XY3), string_to_atom(XY3, Y3), assert(prop(Y3)),
			L = [L1, L2,  Q -> Y2 \/ Y3, Y3 -> Y1, [Y3 -> ^(*(Y2 \/ Y3)), IndM], [Q -> ^(? Y2),IndM]], V =[Y1, Y2, Y3]  
		)
	).*/
	
transF(Q -> ^(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind+1,
	(is_lit(P2), !, N2=N, V3=[], L2=[];
		(N2 is N +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L2 =[], tran2U(Q -> ^(P1 $ P2), N2, IndM, Vx, L), V = [Vx], NM is N + 1;
			 NM is N2 + 1, tran2U(Q -> ^(P1 $ Y2), N2, IndM, Vx, R), append([L2], R, L), V = [Y2, Vx]
	).
	
/*transF([Q -> ^(P1 $ P2), I], Ind, V, N, IndM, NM, L) :-  IndM = Ind,
	(is_lit(P1), !, L1=[], N1=N, V2=[];
		(N1 is N +1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), V2=[Y1], L1=(Y1 -> P1))
	),
	(is_lit(P2), !, N2=N1, V3=[], L2=[];
		(N2 is N1 +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L1=[], (L2=[], tran2U(Q -> ^(P1 $ P2), N, I, Vx, L), V = [Vx], NM is N +1;  
					tran2U(Q -> ^(P1 $ Y2), N2, I, Vx, R1), append([L2], R1, L), V = [Y2, Vx], NM is N2 +1); 
		(L2 =[], tran2U(Q -> ^(Y1 $ P2), N2, I, Vx, R2), append([L1], R2, L), V = [Y1, Vx], NM is N + 1;
			 NM is N2 + 1, string_concat('x', NM, XY3), string_to_atom(XY3, Y3), assert(prop(Y3)),
			L = [L1, L2,  Q -> Y2 \/ Y3, Y3 -> Y1, [Y3 -> ^(*(Y2 \/ Y3)), I], [Q -> ^(? Y2),I]], V =[Y1, Y2, Y3]  
		)
	).*/
	
transF(Q -> ~(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind,
	(is_lit(P2), !, N2=N, V3=[], L2=[];
		(N2 is N +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L2 =[], tran2Uall(Q -> ~(P1 $ P2), N2, IndM, Vx, L), V = [Vx], NM is N + 1;
			 NM is N2 + 1, tran2Uall(Q -> ~(P1 $ Y2), N2, IndM, Vx, R), append([L2], R, L), V = [Y2, Vx]
	).
	
tran2U(Q -> ^(Y1 $ Y2), N, IndM, V, L) :- N1 is N+1, string_concat('x', N1, XY3), 
	string_to_atom(XY3, Y3), assert(prop(Y3)), V= Y3,
	L = [Q -> Y2 \/ Y3, Y3 -> Y1, [Y3 -> ^(*(Y2 \/ Y3)), IndM], [Q -> ^(? Y2),IndM]]. %/

tran2Uall(Q -> ~(Y1 $ Y2), N, IndM, V, L) :- N1 is N+1, string_concat('x', N1, XY3), 
	string_to_atom(XY3, Y3), assert(prop(Y3)), V= Y3,
	L = [Q -> Y2 \/ Y3, Y3 -> Y1, Y3 -> ~(*(Y2 \/ Y3)), Q -> ~(? Y2)]. %/	
	
	

transF(Q -> ^(@P), Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind+1,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, [Y1 -> ^(*Y1), IndM]].
/*transF([Q -> ^(@P),I], Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind+1,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, [Y1 -> ^(*Y1), IndM]].*/
	
transF(Q -> ~(@P), Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, Y1 -> ^(*Y1)].
	
transF(Q -> ^(*P), Ind, V, N, IndM, NM, L) :- IndM is Ind +1,
	(is_dis(P), L = [[Q -> ^(*P), IndM]], NM is N, V=[];
		N1 is N+1, NM=N1,  string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(* Y1),IndM], Y1 -> P]
	).
/*transF([Q -> ^(*P), I], Ind, V, N, IndM, NM, L) :- IndM=Ind,
	(is_dis(P), L = [[Q -> ^(*P),I]];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(* Y1),I], Y1 -> P]
	).*/

transF(Q -> ~(*P), Ind, V, N, IndM, NM, L) :- IndM is Ind,
	(is_dis(P), L = [Q -> ~(*P)], NM is N, V=[];
		N1 is N+1, NM=N1,  string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[Q -> ~(* Y1), Y1 -> P]
	).
	
transF(Q -> ^(?P), Ind, V, N, IndM, NM, L) :- IndM is Ind+1, 
	(is_lit(P), L = [[Q -> ^(?P), IndM]], NM is N, V=[];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(? Y1), IndM], Y1 -> P]
	).
/*transF([Q -> ^(?P), I], Ind, V, N, IndM, NM, L) :- 
	(is_lit(P), IndM=Ind, L = [[Q -> ^(?P), I]];
		N1 is N+1, NM=N1, IndM is Ind+1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(? Y1), IndM], Y1 -> P]
	).*/

transF(Q -> ~(?P), Ind, V, N, IndM, NM, L) :- IndM is Ind, 
	(is_lit(P), L = [Q -> ~(?P)], NM is N, V=[];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[Q -> ^(? Y1), Y1 -> P]
	).
	
	
transF(Q -> P, Ind, V, N, IndM, NM, L) :- IndM=Ind, is_lit(P), V =[], NM =N, L=[Q -> P].
transF(Q, Ind, V, N, IndM, NM, [Q]) :- NM =N, IndM=Ind, V = [].



 %判断是否为文字
 is_lit(C) :- (prop(C); equall(-C, D), prop(D)).
 
 %判断是否是文字的吸取
 is_dis(C) :- is_lit(C).
 is_dis(C) :- C = (P \/ Q), %/
	(is_dis(P), is_dis(Q), !; !, fail).
 