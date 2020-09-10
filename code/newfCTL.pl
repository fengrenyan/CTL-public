:- use_module(wff2cnf).
%:- use_module(isCTLformula).
%:- use_module(tranCTL2SNF).
:- use_module(stepRules).
:- use_module(loopRes).
%:- use_module(simplySNFC).
:- use_module(tempRes).
:- use_module(instantiate).
:- use_module(removeAtom).
:- use_module(replaceTrans).
:- use_module(efImplication).



%:- op(300,fx,@). /*global*/
%:- op(400,fx,$). /*exist*/
%：- op(900,fx, *). /*next*/

:- op(300,fx,@). /*global*/
:- op(300,fx,*). /*next*/
:- op(300,fx,?). /*future*/
:- op(400,xfy,$). /*until*/
:- op(1000,fx, ^). /*exist*/
:- op(1000,fx,~). /*forall*/

:- op(500,fx,-).
%:- op(500,fx,~).
:- op(780,xfy,&).
:- op(790,xfy,\/).%/
:- op(800,xfy,->).
:- op(800,xfy,<->).


:- dynamic(prop/1).
:- dynamic(formula/3).
:- dynamic(pair/2).
:- dynamic(alpha/3).
:- dynamic(beta/3).
:- dynamic(gamma/3).
:- dynamic(snfclause/4).



prop(start).




%将子句集合分为step-clauses 和 temp-clauses并同时生成与temp-clauses对应的新原子。
split2ST([],[],[],[], N).
split2ST([H|L], SL, TL, W, N) :- H = snf_clause(Type, _, _, _),
	(Type = af, H1 =H, N1 is N +1;
		(Type = ef, H1 = H, N1 is N +1; H1 = [], N1 is N
		)
	), split2ST(L, SL1, TL1, W1, N1),
	(H1 =[], TL= TL1, append([H], SL1, SL), X=[], W = W1; 
		string_concat('w', N, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), SL=SL1, append([H], TL1, TL), append([Y1], W1, W)
	). 

%找出L中有原子P出现的clause。
appearing([], _, []).
appearing([H|L], P, R) :- (posC(P, H), H1 = 1; (negC(P, H), H1=1; H1 =[])),
	appearing(L, P, L1),
	(H1 =[], R = L1; append([H], L1, R)).


%找出L中有V中元素出现的clause。
appearing_list([], _, []).
appearing_list(L, [], L).
appearing_list(L, [P|V], R) :- appearing(L, P, R1), appearing_list(L, V, R2), append(R1, R2, R3), sort(R3, R).

%pos(P,C)-------------------------------------------start-------------------------------------------
%deciding p (that should be resolved) appearing in C positively.
posC(P, C) :- C = snf_clause(_, _, H, _), member(P, H).
posC(P, C) :- C = snf_clause(_, _, H, _,_), member(P, H).
%pos-------------------------------------------end-------------------------------------------


%neg-------------------------------------------start-------------------------------------------
%deciding p (that should be resolved) appearing in C negatively.
negC(P, C) :- C = snf_clause(_, _, H, _), F=(-P), member(F, H).
negC(P, C) :- C = snf_clause(_, _, H, _,_), F=(-P), member(F, H).
%neg-------------------------------------------end-------------------------------------------


%all_PosC(L, P, L1)-----------------------------------------start-------------------------------------------
%find all the clauses C in L that P appearing in C positively
all_PosC([], _, []).
all_PosC([H|T], P, L1) :- all_PosC(T, P, Tem), (posC(P, H), append([H], Tem, X), L1=X; L1=Tem).
%all_PosC(L, P, R) :- findall(, posC(P, 
%all_PosC-------------------------------end-------------------------------------


%all_NegC(L, P, L1)-----------------------------------------start-------------------------------------------
%find all the clauses C in L that P appearing in C negatively
all_NegC([], _, []).
all_NegC([H|T], P, L1) :- all_NegC(T, P, Tem), (negC(P, H), append([H], Tem, X), L1=X; L1=Tem).
%all_PosC-------------------------------end-------------------------------------






%------------------------------------start---transCTL2SNF----------------------------------------------

%tran2SNFCl(F, V1, L): transform a CTL formula into a set of snf clauses

tran2SNFClt([], []).
tran2SNFClt([H|L],R) :- tranH2Ct(H, C), tran2SNFClt(L, R1), append([C], R1, R).

tranH2Ct(start -> P, C) :- prop(P), C = snf_clause(start,[start], [P], nil).
tranH2Ct(Q -> P, C) :- is_dis(P), negation([Q], Q1),  wff2cnf(P, P1), P1 = [P2], append(Q1, P2, P3), C = snf_clause(true,[true], P3, nil).
tranH2Ct([Q -> ^(*P),I], C) :- wff2cnf(P, P1), P1 = [P2], C = snf_clause(ex,[Q], P2, I).
tranH2Ct([Q -> ^(?P),I], C) :- wff2cnf(P, P1), P1 = [P2], C = snf_clause(ef,[Q], P2, I).
tranH2Ct(Q -> ~(*P), C) :- wff2cnf(P, P1), P1 = [P2], C = snf_clause(ax, [Q], P2, nil).
tranH2Ct(Q -> ~(?P), C) :- wff2cnf(P, P1), P1 = [P2], C = snf_clause(af,[Q], P2, nil).


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
	
	

	
transF(Q -> ^(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind+1,
	(is_lit(P2), !, N2=N, V3=[], L2=[];
		(N2 is N +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L2 =[], tran2U(Q -> ^(P1 $ P2), N2, IndM, Vx, L), V = [Vx], NM is N + 1;
			 NM is N2 + 1, tran2U(Q -> ^(P1 $ Y2), N2, IndM, Vx, R), append([L2], R, L), V = [Y2, Vx]
	).
	

	
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

	
transF(Q -> ~(@P), Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, Y1 -> ~(*Y1)].
	
transF(Q -> ^(*P), Ind, V, N, IndM, NM, L) :- IndM is Ind +1,
	(is_dis(P), L = [[Q -> ^(*P), IndM]], NM is N, V=[];
		N1 is N+1, NM=N1,  string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(* Y1),IndM], Y1 -> P]
	).


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


transF(Q -> ~(?P), Ind, V, N, IndM, NM, L) :- IndM is Ind, 
	(is_lit(P), L = [Q -> ~(?P)], NM is N, V=[];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[Q -> ~(? Y1), Y1 -> P]
	).
	
	
transF(Q -> P, Ind, V, N, IndM, NM, L) :- IndM=Ind, is_lit(P), V =[], NM =N, L=[Q -> P].
transF(Q, Ind, V, N, IndM, NM, [Q]) :- NM =N, IndM=Ind, V = [].

%------------------------------------end---transCTL2SNF----------------------------------------------


 %判断是否为文字
 is_lit(C) :- (prop(C); equall(-C, D), prop(D)).
 
 %判断是否是文字的吸取
 is_dis(C) :- is_lit(C).
 is_dis(C) :- C = (P \/ Q), %/
	(is_dis(P), is_dis(Q), !; !, fail).



equall(P, P) :- prop(P), !.
equall(-P, -P) :- prop(P), !.
equall(-(-P), P) :- prop(P), !.


%对列表中的元素取反合取：也即是将求子句C的否定\neg C
negation([],[]).
negation([H|T], [H1|T1]) :- 
	equall(- H, H1), 
	negation(T, T1).
	
	
%gain all the propositions in a CTL formula
gain_prop(P & Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), 
	append(L1, L2, L).
gain_prop(P \/ Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), %/
	append(L1, L2, L).
gain_prop(P -> Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), append(L1, L2, L).
gain_prop(^(@P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(-P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(^(P $ Q), L) :- gain_prop(P, L1), gain_prop(Q, L2), append(L1, L2, L3), sort(L3, L).
gain_prop(^(*P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(^(?P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(~(@P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(~(P $ Q), L) :- gain_prop(P, L1), gain_prop(Q, L2), append(L1, L2, L3), sort(L3, L).
gain_prop(~(*P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(~(?P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(P, [P]) :-  atom(P), !, assert(prop(P)).


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




find_Asometime_clauses([], []).
find_Asometime_clauses([C|L1], L2) :- C = snf_clause(Type, X, Y, Z),
	(Type=ex, C1=snf_clause(Type, X, Y, Z,0);
		(Type=ax, C1 =snf_clause(Type, X, Y, Z,0);
			(Type=true, C1 =snf_clause(Type, X, Y, Z,0); C1 =[])
		)
	), find_Asometime_clauses(L1, L3),
	(C1=[], L2=L3; append([C1], L3, L2)).
	
	
%find the set of all global, A-step clauses and E-step clauses with index Ind. （因为对于E-sometime来说，这条路径必须与E-sometime的Ind一致（看参考文献2000））
find_Esometime_clauses([], Ind, []).
find_Esometime_clauses([H|T], Ind, R) :- H = snf_clause(Type, X, Y, Z), 
	(Type = true, !, H1=snf_clause(Type, X, Y, Z,0); 
		(Type = ax, !, H1=snf_clause(Type, X, Y, Z,0);
			(Type = ex, !, (H =snf_clause(ex, _, _, Ind), H1=snf_clause(Type, X, Y, Z,0); H1=[]); H1=[])
		)
	),
	find_Esometime_clauses(T, Ind, T1),
	(H1=[], R = T1; append([H1], T1, R)).



%-------------------------------------------E-loop---start-------2020-4-5------------------------------------------
loopFormula([], _, _, _, false). %为false时不需要做temp-resolution.
loopFormula(L, P, V, Init, F) :- gain_initial_clause(Init, P, C), %P初始时根据future中的文字的正负来的，既原为l,则P为l，Init初始值为[[P]]，V是出现在字句中的命题的集合.
	append(C, L, L1), findFormula(L1, V, H1),
	(H1=[], F=alse; %2020-4-19增加
		(H1=Init, F = H1; (H1 = ture, F=H1; (H1= false, F =false; loopFormula(L, P, V, H1, F))))
	).
	
findFormula(L, V, H) :- loopRes(L, V, R), %write("\nR========="), write(R), %trace, 
	findall(X, (member(X, R), X = snf_clause(true, _, _, _, N), (N =1; N = 2)), R1),
 	subsumeLoop(R1, R1, R1, R2), %write("\nR2========="), write(R2),
	gainH(R2, H).


gainH([], []).
gainH([H|T], [H2|R]) :- H = snf_clause(Type, _, X, L, N),  H2 = X, 
	gainH(T, R).
	
/*gainH([], []).
gainH([H|T], R) :- H = snf_clause(Type, _, X, L, N), 
	(Type = true, ((N =1; N = 2), H2 = X; H2= []); !), 
	gainH(T, T1),
	(H2 = [], R = T1; append([H2], T1, R)).*/

gain_initial_clause([],_, []).
gain_initial_clause([C|L], P, [C1|L1]) :- append([P], C, T), sort(T, T1), C1 = snf_clause(ax, [], T1, nil, 2), 
	gain_initial_clause(L, P, L1).
	
%-------------------------------------------E-loop---end-------------------------------------------------



%-------------------------simplify-----------------start-------------------------------------------

simp_disSet([],[]). %[]表示的子句为false，也即是不包含任何文字的子句为false.
simp_disSet(L, L1) :- (member(P, L), member(-P, L), L1= [true]; 
	(member(true, L), L1=[true]; 
		(member(false, L), delete(L, false, L2), sort(L2, L1); sort(L, L1))
	)
	). %注意负号与数字之间的距离

simp_conSet([], [true]).%[]表示的term为TRUE，也即是不包含任何文字的子句为TRUE
simp_conSet(L, L1) :- (member(P, L), member(-P, L), L1= [false]; 
	(member(false, L), L1 =[false]; 
		(member(true, L), delete(L, true, L2), sort(L2, L1); sort(L, L1))
	)
	). %注意负号与数字之间的距离

elimElement(H, [], []).
elimElement(H, [H1|T1], L1) :- elimElement(H, T1, L2), 
	(H = H1, L1=L2; append([H1], L2, L1)).
	
	
%化简子句本身
%普通子句
simplySNFC(C, C1) :- C= snf_clause(Type, H, T, L), 
	(Type = true, simp_disSet(T, T1), C1=snf_clause(Type, H, T1, L);
	simp_conSet(H, H1), simp_disSet(T, T1), C1=snf_clause(Type, H1, T1, L)). 
%loop子句	
simplySNFCLoop(C, C1) :- C= snf_clause(Type, H, T, L, N),
	(Type = true, !, simp_disSet(T, T1), C1=snf_clause(Type, H, T1, L,N);
	simp_conSet(H, H1), simp_disSet(T, T1), C1=snf_clause(Type, H1, T1, L,N)). 


%子句之间的Subsume
%subsume rules
subsume1(X, Y) :- X = snf_clause(_, H1, T1, _), Y = snf_clause(_, H2, T2, _), subset(T1, T2). %(i)(ii)(v)(vi)(vii)都适用

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
subsume([H|L], X, Y, R) :- subsume_list(H, X, Y, L1), %初始调用时，X=Y=[H|L]
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


%------------------------simplify-----------------end-------------------------------------------

obtainAtom([],[]).
obtainAtom([H|T], [H1|L1]) :- (prop(H), H1=H; H = - H1), obtainAtom(T, L1).


base(R) :- findall([P, L], (pair(P, L), assert(formula(snf, P, L))), R).
base(V1, R) :- findall([P, L], pair(P, L), R1), 
	(R1=[], R=[];
		deleteTnest(R1, V1, R)
	).
	
%删除嵌套变量的true子句。
nestFormula([], _, []).
nestFormula([H|T], V1, [H1|L1]) :- H = formula(Type, X, L),
	(Type = con, nest_list(L, V1, L2), H1 = formula(Type, X, L2); H1 = H), nestFormula(T, V1, L1).

deleteTnest([], _, []).
deleteTnest([H|T], V1, [H1|L1]) :- H =[P, L], H1=P, nest_list(L, V1, L2), assert(formula(snf, P, L2)),
	deleteTnest(T, V1, L1).
	
nest_list([], _, []).
nest_list([H|T], V1, L) :- H=(Type, Q, I), obtainAtom(Q, Q1), intersection(V1, Q1, Q2), subtract(Q1, Q2, Q3),
	%(Type=true, obtainAtom(Q, Q1), (intersection(V1, Q1,[]), C1=H; C1=[]);
	(Type=true, (Q2=[], C1=H; C1=[]);
		((Type = ax; Type = ex), (Q2 =[], C1=H; (Q3 =[], C1=H; C1 =[])); %2020-5-2添加这部分，删除b,c型的子句。
			C1=H
		)   
	), nest_list(T, V1, L1),
	(C1=[], L=L1; append([C1], L1, L)).


sat(F) :- (gain_prop(F, P), L=[start-> z, z -> F], assert(prop(z)), 
	tran2SNF(L, 0, 0, V1, SNF), tran2SNFClt(SNF, LC), append(P, V1, V2), append([z], V2, V3), %res(LC, V3, R),
	split2ST(LC, SL, TL, W, 0),
	step_resolution(SL, V3, L2),
	(L2=false, write("\n **unsat \n"); 
		temp_resolution(TL, W, L2, V3, R1, TL1, W1, V3), append(V3, W, V5),
		append(L2, LC, L3), append(L3, R1, R2), sort(R2, R3), split2ST(R3, SL2, TL2, W2, 0), step_resolution(SL2, V5, R4),
		(R4 = false,  write("\n **unsat \n"); write("\n sat \n"))
	); write("This formula is error! Please input the right formula.")).
	
	
sAt(F) :- gain_prop(F, P1), L=[start-> z, z -> F], assert(prop(z)), sort(P1, P), write("atoms in F:"), write(P),
	tran2SNF(L, 0, 0, V1, SNF), write("\n New atoms:"), write(V1),
	tran2SNFClt(SNF, LC), write("\n SNF: "), write(SNF),
	write("\n Normal form:"), write(LC),
	append(P, V1, V2), append([z], V2, V3), res(LC, V3, R),
	(R=false, write("\n *****unsat \n"); write("\n -----------------result-----------------\n"),
	write(R),
	write("\n -----------------result-----------------\n"),
	write("\n ####sat \n")).
	
res(L, V3,  R) :- split2ST(L, SL, TL, W, 0), step_resolution(SL, V3, L2), 
	(L2=false, R=false; 
		temp_resolution(TL, W, L2, V3, R1, TL1, W1, V3), append(V3, W, V5), append(L2, L, L3), 
			append(L3, R1, R2), sort(R2, R3),
			(R3=L, R = R3; res(R3, V5, R))
	).



removeSing([],[]).
removeSing([H|L], R) :- H = snf_clause(Type, Q, T, I), length(Q, N),
	(N=1, H1=[]; H1=H),
	removeSing(L, R1),
	(H1=[], R=R1; append([H1], R1, R)).


ctlForget(F, V, R) :- (gain_prop(F, P), L=[start-> z, z -> F], assert(prop(z)), 
	tran2SNF(L, 0, 0, V1, SNF), tran2SNFClt(SNF, LC), append(V, V1, V2), append([z], V2, V3), 
	appearing_list(LC, V, L1), split2ST(L1, SL, TL, W, 0), %trace, 
	write("\n V======"), write(V),
	write("\n SNF======"), write(L1),
	step_resolution(SL, V, L2),
	write("\n Res======"), write(L2),
	write("\n TL======="), write(TL),
	%ctlForget_list(SL, TL, W,V2, L2),
	append(V3, W, V6),
	(L2=false, R = false; append(V3, P, V4), sort(V4, V5), temp_resolution(TL, W, L2, V, R1, TL1, W1, V5), 
		append(L2, LC, L3), append(L3, R1, R2), sort(R2, R3), split2ST(R3, SL2, TL2, W2, 0), step_resolution(SL2, V, R4), %trace, 
		(R4 = false, R = false;
		 append(R4, TL2, Ry), subtract(Ry, [snf_clause(true,[true], [true], nil)], R44),
		 removeAtom(R44,V,R55),   %trace, write(O0),
		 snftoCTL(R55, F1, F2), 
		 %toCTL(FRR, V, V1, CTL),
		 write("\n =======CTL ========\n"), write(R55), write("\n"), write(F2),
		  write("\n =======CTL ========\n"),
		write("\n W====="), write(W1))
	); %其中W是与TL中子句对应的新的原子命题，R1是结果，TL1是找到loop formula的子句的集合， W1对应TL1，V5是计算loop formula是需要的命题的集合。
	%(L2=false, R = false; append(L2, LC, L3), sort(L3, R));
	write("This formula is error! Please input the right formula.")).
	
	
/*	conLit([],true, true).
conLit([H|L], F1, F) :- 
	conLit(L, CTL, R), (CTL=true, F = H, F1=H; F = (H & CTL), F1=F).*/
	
snftoCTL([], true, true).
snftoCTL([C|R], F1, F2) :- snftoCTL(R, CTL1, CTL2), 
	C = snf_clause(Type, T, H, nil), 
	(Type = start, disLit(H, H1, H2), (CTL1 = true, F2 = H2, F1=H2; F2 = (H2 & CTL1), F1 = F2);
		(Type = true, disLit(H, H1, H2), (CTL1 = true, F2 = (~(@(H2))), F1=F2; F2 = ((~(@(H2))) & CTL1), F1 = F2);
			(conLit(T, T1, T2), disLit(H, H1, H2),
				(Type = ax,  H3 = (~(*(H2))); 
					Type=af, H3 = (~(?(H2)))
				), (CTL1 = true, F2 = (~(@(T2 -> H3))), F1=F2; F2 = ((~(@(T2 -> H3))) & CTL1), F1 = F2);
				F1 = true, F2= true
			)
		)
	).
	
snftoF([], []).
snftoF([C|R], [C1|F]) :- C = snf_clause(Type, T, H, nil), disLit(H, H1, H2),
	(Type = start,  C1= H2;
		(Type = true, C1 = (~(@(H2)));
			(Type = ax,  H3 = (~(*(H2))), conLit(T, T1, T2), C1 = (~(@(T2 -> H3))); 
				Type=af, H3 = (~(?(H2))), conLit(T, T1, T2), C1 = (~(@(T2 -> H3)))
			)
		)
	), snftoF(R, F).
	


/*实现将formla(Type, Q, L)公式转换为CTL公式toCTL(L, V, V1, F)：
其中，L是formla(Type, Q, L)公式的集合，V为需要遗忘的原子命题的集合，V1是新引入的原子命题的集合。
该过程分为以下两步：
(1) 将Type=con的公式按照从端点变量(end)到初始变量(first)的顺序实例化——使得对每个变量的实例化公式中不出现
其他新引入的变量：该过程由end2first(L, V, V1, CTL, CTLcon)完成，初始时CTL=[]表示还没有被转换为ctlformula的
公式并用来记录已经转换为ctlformula的公式的集合（用于记录每个V1中每个变量的实例化），CTLcon是计算结果（是V1中每个变量的
ctlformula公式的集合）；
（2）将Type为其它类型的formula转换为ctlformula，为了方便查看，目前还没将其中的V1中的变量替换。
*/
toCTL([], _, _, []).
toCTL(L, V, V1, F) :- obtainAB(AB), end2first(L, V, V1, [], CTLcon),
	(AB=[], toCTL_list(L, CTLcon, F1), append(F1, CTLcon, FF), toCTL_temprol(L, F1, F2), append(F2, F1, F); 
		replaceAB(L, AB, R1), toCTL_list(R1, CTLcon, F1), append(F1, CTLcon, FF), toCTL_temprol(L, F1, F2), append(F2, F1, F)).
		
/*toCTL(L, F) :- obtainAB(AB), 
	(AB=[], toCTL_list(L, F1), toCTL_temprol(L, F1, F2), append(F2, F1, F); 
	replaceAB(L, AB, R1), toCTL_list(R1, F1), toCTL_temprol(R1, F1, F2), append(F2, F1, F)).*/
	

%T为formula公式的集合，初始时F为空
end2first(T, V, V1, F, CTLcon) :-  
	(V1 =[], !, CTL=[], CTLcon=[];
		%findall([Q,L], (member(formula(con, Q, L), T), isend(L, V, V1)), EL), 
		findEnd(T, V, V1, EL), 
		(EL= [], !, CTL=[], CTL1=[]; 
			con2ctl(EL, F, V2, CTL), subtract(V1, V2, V11), append(F, CTL, F1), end2first(T, V, V11, F1, CTL1)),
		(CTL=[], CTLcon=[]; append(CTL, CTL1, CTL2), sort(CTL2, CTLcon))
	).

findEnd([], _, _, []).
findEnd([H1|L1], V, V1, EL) :- H1 = formula(Type, Q, L),
	(Type=con, 
		(isend(L, V, V1), H2=[Q, L]; H2 = []); H2=[]),
	findEnd(L1, V, V1, EL1),
	(H2=[], EL=EL1; append([H2], EL1, EL)).
		 

con2ctl([], _, [], []).
con2ctl([H1|L1], F, [Q|LL], [H2|L2]) :- H1=[Q, L], conCTL(L, F, F1), H2 = ctlformula(Q, F1), con2ctl(L1, F, LL, L2) .


%计算列表中clause的合取
conCTL([],_, true).
conCTL([H|L], CTL, F) :- H = (Type, T, I), disCTL(T, CTL, T1),
	(Type=ex, T2=(^(*(T1)));
		(Type=ax, T2=(~(*(T1)));
			(Type=ef, T2=(^(?(T1)));
				(Type=af, T2=(~(?(T1)));
					T2 =T1
				)
			)
		)
	),
	conCTL(L, CTL, F1), (F1=true, F=T2; F = (T2 & F1)).

%计算列表中文字的吸取	
disCTL([], _, false).
disCTL([H|L], CTL, F) :- equall(- H, X), disCTL(L, CTL, F1),
	((member(ctlformula(H, F2), CTL), F3=F2; member(ctlformula(X, F2), CTL), F3=(- F2)), (F1=false, F=F3; F = (F3 \/ F1)); %/
		(F1=false, F=H; F = (H \/ F1)) %/
	).
/*disCTL([H|L], CTL, F) :- equall(- H, X), 
	((member(ctlformula(H, F2), CTL); member(ctlformula(X, F2), CTL)), disCTL(L, CTL, F1), (F1=false, F=F2; F = (F2 \/ F1)); %/
		disCTL(L, CTL, F1), (F1=false, F=H; F = (H \/ F1)) 
	).*/


%计算列表中文字的合取
conLit([],true, true).
conLit([H|L], F1, F) :- 
	conLit(L, CTL, R), (CTL=true, F = H, F1=H; F = (H & CTL), F1=F).
	
	
%计算列表中文字的吸取
disLit([],false, false).
disLit([H|L], F1, F) :- 
	disLit(L, CTL, R), (CTL=false, F = H, F1=H; F = (H \/ CTL), F1=F). %/


%判断变量是不是端点变量，也即是在trans过程中引入的最后一个变量
isend([], _, _).
isend([H|T], V, V1) :- H=(Type, L, I), obtainAtom(L, L1), 
	(intersection(L1, V, []), intersection(L1, V1, []), !; !, fail).


%将Type为非con类型的formula转换为ctlformula，为了方便查看，目前还没将其中的V1中的变量替换。
toCTL_temprol([], _, []).
toCTL_temprol([H|T], Con, R) :- H = formula(Type, Q, L), 
	((Type = con; (Type = alpha; Type = beta)), H1=[];
		(Type = af, L=[(X, nil)], disjunction(X, X1), H2=(~(? X1)), H1=ctlformula(Q, H2);
			(Type = ef, L=[(X, I)], disjunction(X, X1), H2=(^(? X1)), H1=ctlformula(Q, H2);
				(Type = ax, L=[(X, nil)], disjunction(X, X1), H2=(~(* X1)), H1=ctlformula(Q, H2);
					(Type = ex, L=[([X], I)], member(ctlformula(X, X1), Con), H2=(^(* X1)), H1=ctlformula(Q, H2);
						(Type = au, L=[([X], [Y], I)], member(ctlformula(X, X1),Con), 			
							member(ctlformula(Y, Y1), Con), H2 = (~(X1 $ Y1)), H1=ctlformula(Q, H2);
							(Type = eu, L=[([X], [Y], I)], member(ctlformula(X, X1),Con), 			
								member(ctlformula(Y, Y1), Con), H2 = (^(X1 $ Y1)), H1=ctlformula(Q, H2);
								(Type=ag, L=[([X], I)], member(ctlformula(X, X1), Con), H2=(~(@ X1)), H1 = ctlformula(Q, H2);
									(Type=eg, L=[([X], I)], member(ctlformula(X, X1), Con), H2=(^(@ X1)), H1 = ctlformula(Q, H2);
										H1=[]
									)
								)
							)					
						)
					)
				)
			)
		)
	), toCTL_temprol(T, Con, R1),
	(H1=[], R=R1; append([H1], R1, R)).


%将类型为con、alpha、beta的formula公式转换为ctlformula，对于con的情形可能会与之前的end2first的情形重复。
%其中，CTLcon是end2first得到的结果。
toCTL_list([],_,[]).
toCTL_list([H|L], CTLcon, R) :-  H = formula(Type, X, LL),  
	(Type=con, conCTL(LL, CTLcon, F1), H1=ctlformula(X, F1);
		(Type=alpha, conA(LL, CTLcon, F1), H1=ctlformula(X, F1);
			(Type=beta, conB(LL, CTLcon, F1), H1=ctlformula(X, F1); H1=[])
		)
	), 
	toCTL_list(L, CTLcon, R1),
	(H1=[], R=R1; append([H1], R1, R)).
	
%对alpha类型的formula进行求解CTLformula	
conA([], _, true).
conA([H1, H2|L], CTLcon, F) :- H1 = [[C3,C2],I,[C33,C2,C4],[C2,C3]], append(C3, C2, C32), 
	append(C33, C2, C332), append(C332, C4, C3324), append(C3324, H2, CH2),
	disCTL(C32, CTLcon, F1), disCTL(CH2, CTLcon, F2), F3=(F1 \/ (^(*(F2 \/ ~(*(~(? F1))))))), %/
	conCTL(L, CTLcon, F4), F = (F3 & F4).
	
%对beta类型的formula进行求解CTLformula	
conB([], _, true).
conB([H1, H2|L], CTLcon, F) :- H1 = [[C3,C2],I,[C33,C2,C4],[C2,C3]], append(C3, C2, C32), 
	append(C33, C2, C332), append(C332, C4, C3324), append(C3324, H2, CH2),
	disCTL(C32, CTLcon, F1), disCTL(CH2, CTLcon, F2), %trace, simpDis(F1, F11), simpDis(F2, F22),
	F3=(F1 \/ (~(*(F2 \/ ~(*(~(? F1))))))), %/
	conCTL(L, CTLcon, F4), F = (F3 & F4).
	
	

conjunction([], true).
conjunction([H|L], F) :- H = (Type, T, I), disjunction(T, T1),
	(Type=ex, T2=(^(*(T1)));
		(Type=ax, T2=(~(*(T1)));
			(Type=ef, T2=(^(?(T1)));
				(Type=af, T2=(~(?(T1)));
					T2 =T1
				)
			)
		)
	),
	conjunction(L, F1), (F1=true, F=T2; F = (T2 & F1)).
	
disjunction([], false).
disjunction([H|L], F) :-  disjunction(L, F1), (F1 = false, F = H; F = (H \/ F1)). %/



%该过程用来寻找formula公式集合R中用alpha或者beta公式（看看是否有gamma公式）替换的原子命题。
obtainAB(R) :- findall(X, efImplication:alpha(_, X,_), R1), findall(Y, efImplication:beta(_, Y, _), R2), append(R1, R2, R).

%将formula(Type, X, L)中X有alpha或者beta公式（看看是否有gamma公式）的公式转换为Type为alpha或者beta（看看是否有gamma）的形式，
%以便后面计算的时候方便分类处理。
replaceAB([], _, []).
replaceAB([H1|L1], AB, [H2|R1]) :- H1 = formula(Type, X, L),
	(Type=con, (member(X, AB), efImplication:snfclause(Type1, [X], T, I), 
		(Type1 = ex, 
			(member([N, alpha], T), efImplication:alpha(N, X, T2),  %T2=[
				subtract(T, [[N, alpha]], T3), append([T2], [T3], T33), 
				subtract(L, [(ex, T3, I)], LX), append(T33, LX, LL),
				H2 = formula(alpha, X, LL));
			(Type1=ax, (member([N, beta], T), efImplication:beta(N, X, T2),
				subtract(T, [[N, beta]], T3), append([T2], [T3], T33), 
				subtract(L, [(ax, T3, I)], LX), append(T33, LX, LL),
				H2 = formula(beta, X, LL)); H2=H1)
		); H2=H1); H2=H1),
	replaceAB(L1, AB, R1).
	%(H2=[], R=R1; append([H2],  R1, R)).
			


