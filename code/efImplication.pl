

%EF-implication


:- module(efImplication, [fImp/5]).

/*对每个sometimes子句寻找对应的满足EF规则的前提条件，然后将得到的结果保存在为snfclause、alpha和beta对，等到最后在进行替换。
*/

%为每一种sometimes子句写一个过程寻找满足需要的前提。
efImp_Esome(H, L, NIV, IV, N, N1) :-  H = snf_clause(ef, Q, T, I), T = [X], equall(- X, Y), 
	findall([Q, C2, C3, C4, I1], (member(snf_clause(true, [true], T1,nil), L), member(Y, T1), subtract(T1, [Y], L1), 
	obtainAtom(L1, L2), intersection(L2, NIV, L3), not(L3 =[]), pair(X, T2),
	(member(snf_clause(ex, Q, T3,I),L), I1=I; member(snf_clause(ax, Q, T3, nil),L), I1=nil), 
	%(member(snf_clause(ex, Q, T3,I1),L); member(snf_clause(ax, Q, T3, nil),L), I1=nil), 
	(member(X1, T3), obtainAtom([X1], Lx), Lx =[XX],member(XX, L3), equall(- X1, X2), member(X2,L1)), %L1的寻找
	subtract(L1, [X2],C2), subtract(T2, C2, C3), subtract(T3, [X1], C4)), F),
	(F=[], !, N1 = N; addGamma(F, N), length(F, N2), N1 is N+N2).
	
	
efImp_Esome(H, L, NIV, IV,N, N1) :-  H = snf_clause(ef, Q, T, I1), 
	 conditionEf(H, L, L, NIV,IV, F), %trace, write("\n $$$F====="), write(F),
	delete(F, [], F1), 
	(F1=[], !, N1=N; addaf(Q, F1, N), length(F1, N2), N1 is N+N2).
	

conditionEf(_, [], _, _, _, []).
conditionEf(H, [H1|L11], L, NIV, IV, R) :- H = snf_clause(af, Q, T, I), T = [X], equall(- X, Y), 
	((H1=snf_clause(ex, Q, T3,I),L), I1=I; H1=snf_clause(ax, Q, T3, nil), I1=nil), 
		(member(snf_clause(true, [true], T1,nil), L), member(Y, T1), subtract(T1, [Y], L1), 
			obtainAtom(L1, L2), intersection(L2, NIV, L3), not(L3 =[]), pair(X, T2),
	%(member(snf_clause(ex, Q, T3,I),L); member(snf_clause(ax, Q, T3, I),L)), 
			(member(X1, T3), obtainAtom([X1], Lx), Lx =[XX], member(XX, L3), equall(- X1, X2), member(X2,L1)), %L1的寻找
			subtract(L1, [X2],C2), subtract(T2, C2, C3), subtract(T3, [X1], C4), 
			append([Y], C2, Ly), append(Ly, C4, Yy),
			(I1=nil, H2 = snf_clause(ax, Q, Yy, I1); H2 = snf_clause(ex, Q, Yy, I1)),
			C1=[Q, C2, C3, C4, I1,H2]; C1=[]);
		C1=[]
	), conditionEf(H, L11, L, NIV, IV, R1),
	(C1=[], R=R1; append([C1], R1, R2), sort(R2, R)).
	

addGamma([]).
addGamma([H|T], N) :- H=[Q, C2, C3, C4,I,H1], Q =[X], (C2=[]; C2 = [(_, T2, _)]), (C3=[]; C3=[(_, T3, _)]), (C4=[];C4 = (_, T4, _)),
	negation(T2, C22), negation(T3, C33), negation(T4, C44),
	%assert(gamma(N, X, [[C22, C33], I, [T3, C22, C44],[T2, T3]])),
	assert(gamma(N, X, [[T3, T2], I, [C33, T2, T4],[T2, T3]])),
	H1 = snf_clause(ax, Q, T, I), retractall(H1), append([[N, beta] ], T, T5), assert(snfclause(ax, Q, T5, I))
	N1 is N+1,
	addGamma(T, N1).
	

afImp_Asome(H, L, NIV, IV,N, N1) :-  H = snf_clause(af, Q, T, I1), 
	/*T = [X], equall(- X, Y), 
	findall([C2, C3, C4, I], (member(snf_clause(true, [true], T1,nil), L), member(Y, T1), subtract(T1, [Y], L1), 
	obtainAtom(L1, L2), intersection(L2, NIV, L3), not(L3 =[]), pair(X, T2),
	(member(snf_clause(ex, Q, T3,I),L); member(snf_clause(ax, Q, T3, I),L)), 
	(member(X1, T3), obtainAtom([X1], Lx), Lx =[XX], member(XX, L3), equall(- X1, X2), member(X2,L1)), %L1的寻找
	subtract(L1, [X2],C2), subtract(T2, C2, C3), subtract(T3, [X1], C4)), F),*/
	 conditionAf(H, L, L, NIV,IV, F), %trace, write("\n $$$F====="), write(F),
	delete(F, [], F1), 
	(F1=[], !, N1=N; addaf(Q, F1, N), length(F1, N2), N1 is N+N2).
	


	

conditionAf(_, [], _, _, _, []).
conditionAf(H, [H1|L11], L, NIV, IV, R) :- H = snf_clause(af, Q, T, I1), T = [X], equall(- X, Y), 
	((H1=snf_clause(ex, Q, T3,I); H1 = snf_clause(ax, Q, T3, I)),
		(member(snf_clause(true, [true], T1,nil), L), member(Y, T1), subtract(T1, [Y], L1), 
			obtainAtom(L1, L2), intersection(L2, NIV, L3), not(L3 =[]), pair(X, T2),
	%(member(snf_clause(ex, Q, T3,I),L); member(snf_clause(ax, Q, T3, I),L)), 
			(member(X1, T3), obtainAtom([X1], Lx), Lx =[XX], member(XX, L3), equall(- X1, X2), member(X2,L1)), %L1的寻找
			subtract(L1, [X2],C2), subtract(T2, C2, C3), subtract(T3, [X1], C4), 
			append([Y], C2, Ly), append(Ly, C4, Yy),
			(I=nil, H2 = snf_clause(ax, Q, Yy, I); H2 = snf_clause(ex, Q, Yy, I)),
			C1=[C2, C3, C4, I, H2]; C1=[]
		);
		C1=[]
	), conditionAf(H, L11, L, NIV, IV, R1),
	(C1=[], R=R1; append([C1], R1, R2), sort(R2, R)).
	



addaf(Q, [],_).
addaf(Q, [H|T], N) :- H=[C2, C3, C4,I,H1],  
	(I=nil, addBeta(Q, H,N); addAlpha(Q, H,N)), N1 is N+1, addaf(Q, T,N1).
	
addBeta(Q, H,N) :- H=[C2, C3, C4,I, H1], Q =[X], (C2=[]; C2 = [(_, T2, _)]), (C3=[]; C3=[(_, T3, _)]), (C4=[];C4 = (_, T4, _)),
	negation(T2, C22), negation(T3, C33), negation(T4, C44),
	%assert(beta(N, X, [[C22, C33], I, [T3, C22, C44],[T2, T3]])),
	assert(beta(N, X, [[T3, T2], I, [C33, T2, T4],[T2, T3]])),
	%(H1=snf_clause(ex, Q, T3,I), retractall(H1), append([beta], T3, T5), assert(snfclause(ex, Q, T5, I)); 
	H1 = snf_clause(ax, Q, T, I), retractall(H1), append([[N, beta] ], T, T5), assert(snfclause(ax, Q, T5, I)).
	
addAlpha(Q, H, N) :- H=[C2, C3, C4,I,H1], Q =[X], (C2=[]; C2 = [(_, T2, _)]), (C3=[]; C3=[(_, T3, _)]), (C4=[];C4 = (_, T4, _)),
	negation(T2, C22), negation(T3, C33), negation(T4, C44),
	%assert(alpha(N, X, [[C22, C33], I, [T3, C22, C44],[T2, T3]])),
	assert(alpha(N, X, [[T3, T2], I, [C33, T2, T4],[T2, T3]])),
	H1=snf_clause(ex, Q, T,I), retractall(H1), append([[N, alpha]], T, T5), assert(snfclause(ex, Q, T5, I)).
	


%写一个过程调用上面两个过程, IV表示已经被实例化的命题的集合， NIV = V \/ V1。/
fImp([], _, _,_,_).
fImp([H|TL], L, NIV, IV, N) :- H = snf_clause(Type, Q, T, I), obtainAtom(T, R1), intersection(R1, IV, R2),
(R2=[], !; %表示该sometimes子句是被计算resolution的字句且变量为新引入的变量才做下面的过程。
	(Type = ef, efImp_Esome(H, L, NIV, IV,N,N1); afImp_Asome(H, L, NIV, IV,N,N1)),
	N2 is N1+1,
	fImp(TL, L, NIV,IV, N2)
).
