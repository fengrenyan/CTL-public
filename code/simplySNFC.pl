

:- module(simplySNFC, [simplySNFC/2, subsume/4, subsumeLoop/4]).



simp_disSet([],[false]).
simp_disSet(L, L1) :- (member(P, L), member(-P, L), L1= [true]; 
	(member(true, L), L1=[true]; 
		(member(false, L), elimElement(false, L, L2), sort(L2, L1); sort(L, L1))
	)
	). %注意负号与数字之间的距离

simp_conSet([], [true]).
simp_conSet(L, L1) :- (member(P, L), member(-P, L), L1= [false]; 
	(member(false, L), L1 =[false]; 
		(member(true, L), elimElement(true, L, L2), sort(L2, L1); sort(L, L1))
	)
	). %注意负号与数字之间的距离


%化简子句本身
simplySNFC(C, C1) :- C= snf_clause(Type, H, T, L), simp_conSet(H, H1), simp_disSet(T, T1), C1=snf_clause(Type, H1, T1, L).



%子句之间的Subsume
%subsume rules
subsume1(X, Y) :- X = snf_clause(_, H1, T1, _), Y = snf_clause(_, H2, T2, _), subset(T1, T2). %(i)(ii)(v)(vi)(vii)都使用

subsume2(X, Y) :- X = snf_clause(_, H1, T1, _), Y = snf_clause(_, H2, T2, _), subset(T1, T2), subset(H1, H2).

subsume3(X, Y) :- X = snf_clause(_, H1, T1, _, _), Y = snf_clause(_, H2, T2, _,_), subset(T1, T2).


subsumeLoop([], _, L, L).
subsumeLoop(_, [], [], []).
subsumeLoop([H|L], X, Y, R) :- subsumeLoop_list(H, X, Y, L1), 
	(L1 = X, subsumeLoop(L, L1, L1, R); subsumeLoop(L1, L1, L1, R)).


subsumeLoop_list(C, [], L, L).
subsumeLoop_list(C, [H|T], L, R) :- (C = H, subsumeLoop_list(C, T, L, R); 
    ((subsume3(C, H), delete(L, H, L1); L1 = L),
	    subsumeLoop_list(C, T, L1, R)
    )).




subsume([], _, L, L).
subsume(_, [], [], []).
subsume([H|L], X, Y, R) :- subsume_list(H, X, Y, L1), 
	(L1=X, subsume(L, L1, L1, R); subsume(L1, L1, L1, R)).


subsume_list(C, [], L, L).
subsume_list(C, [H|T], L, R) :- (C = H, subsume_list(C, T, L, R); 
(C = snf_clause(Type1,_,_,_), H=snf_clause(Type2,_,_,_), %judgeType(C, Type1), judgeType(H, Type2), 
	(Type1 = ax, !, (Type2=ax, !, (subsume2(C, H), delete(L, H, L1); L1 = L); (Type2 =ex, !, (subsume2(C, H), delete(L, H, L1); L1 = L ); (Type2=true, !, (subsume1(H, C), delete(L, C, L1); L1 = L); L1=L))); 
		(Type1=ex, !, (Type2=ax, !,(subsume2(H, C), delete(L, C, L1); L1 = L); (Type2 =ex, !, (subsume2(C, H), delete(L, H, L1); L1 = L); (Type2=true, !, (subsume1(H, C), delete(L, C, L1); L1 = L); L1=L)));
			(Type1 =true, !, ((Type2=start; Type2=ax; Type2=ex; Type2=true), (subsume1(C, H), delete(L, H, L1); L1 = L));
				/*(Type2=start, !, (subsume1(C, H), delete(H, L, L1); L1 = L); (Type2=ax, !, (subsume1(C, H), delete(H, L, L1); L1 = L); (Type2=ex, !, (subsume1(C, H), delete(H, L, L1); L1 = L); (Type2=true, !, (subsume1(C, H), delete(H, L, L1); L1 = L); L1 = L))));*/
				(Type1 =start, !, (Type2=start, !, (subsume1(C, H), delete(L, H, L1); L1 = L); (Type2=true, !, (subsume1(H, C), delete(L, C, L1); L1 = L); L1 = L)); L1 = L)
			)
		)
	),
	subsume_list(C, T, L1, R)
)).
