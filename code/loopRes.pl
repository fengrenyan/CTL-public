

:- module(loopRes, [loopRes/3]).


%resolution ----------------------------------------------------------start--------------------
%step rules


unionC(C1, C2, P, X) :- equall(P, F1), delete(C1, F1, X1), equall(-P, F2), delete(C2, F2, X2), append(X1, X2, X3), sort(X3, X).
union(C1,C2,R) :- append(C1,C2,R1), sort(R1, R).

%SRES1
res_SRES1(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_, X1), C2=snf_clause(_,T2, H2,_,X2), (X1 > X2, N=X1; N=X2),
	union(T1,T2,T), unionC(H1,H2,P,H), R1=snf_clause(ax,T,H, nil, N), simplySNFCLoop(R1, R).
	
%SRES2
res_SRES2(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,I,X1), C2=snf_clause(_,T2, H2,_,X2), (X1 > X2, N=X1; N=X2),
	union(T1,T2,T), unionC(H1,H2,P,H), R1=snf_clause(ex,T,H,I,N), simplySNFCLoop(R1, R).
	
%SRES3
res_SRES3(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,I,X1), C2=snf_clause(_,T2, H2, I,X2), (X1 > X2, N=X1; N=X2),
	union(T1,T2,T), unionC(H1,H2,P,H), R1=snf_clause(ex, T,H,I, N), simplySNFCLoop(R1, R).
	
%SRES4
/*res_SRES4(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_), C2=snf_clause(_,T2, H2,_),
	unionC(H1,H2,P,H), R=snf_clause(start,T1,H,nil).*/
	
%SRES5
/*res_SRES5(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_), C2=snf_clause(_,T2, H2,_),
	unionC(H1,H2,P,H), R=snf_clause(start,T2,H,nil).*/
	
 %SRES6
res_SRES6(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_,_), C2=snf_clause(_,T2, H2,_,_),
	unionC(H1,H2,P,H), (H = [], R1=snf_clause(ax,T2,H,nil, 3), simplySNFCLoop(R1, R); R1=snf_clause(ax,T2,H,nil, 2), simplySNFCLoop(R1, R)).
	
%SRES7
res_SRES7(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_,_), C2=snf_clause(_,T2, H2, I,_),
	unionC(H1,H2,P,H), (H=[], R1=snf_clause(ex,T2,H,I,3), simplySNFCLoop(R1, R); R1=snf_clause(ex,T2,H,I,2), simplySNFCLoop(R1, R)).
	
%SRES8
res_SRES8(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_, X1), C2=snf_clause(_,T2, H2,_,X2), (X1 > X2, N=X1; N=X2),
	unionC(H1,H2,P,H), R1=snf_clause(true,T2,H,nil,N), simplySNFCLoop(R1, R).
	
	
%%%%不化简字句的情况
	/*%SRES1
res_SRES1(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_, X1), C2=snf_clause(_,T2, H2,_,X2), (X1 > X2, N=X1; N=X2),
	union(T1,T2,T), unionC(H1,H2,P,H), R=snf_clause(ax,T,H, nil, N).
	
%SRES2
res_SRES2(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,I,X1), C2=snf_clause(_,T2, H2,_,X2), (X1 > X2, N=X1; N=X2),
	union(T1,T2,T), unionC(H1,H2,P,H), R=snf_clause(ex,T,H,I,N).
	
%SRES3
res_SRES3(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,I,X1), C2=snf_clause(_,T2, H2, I,X2), (X1 > X2, N=X1; N=X2),
	union(T1,T2,T), unionC(H1,H2,P,H), R=snf_clause(ex, T,H,I, N).*/
	
%SRES4
/*res_SRES4(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_), C2=snf_clause(_,T2, H2,_),
	unionC(H1,H2,P,H), R=snf_clause(start,T1,H,nil).*/
	
%SRES5
/*res_SRES5(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_), C2=snf_clause(_,T2, H2,_),
	unionC(H1,H2,P,H), R=snf_clause(start,T2,H,nil).*/
	
%SRES6
/*res_SRES6(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_,_), C2=snf_clause(_,T2, H2,_,_),
	unionC(H1,H2,P,H), (H = [], R=snf_clause(ax,T2,H,nil, 3); R=snf_clause(ax,T2,H,nil, 2)).
	
%SRES7
res_SRES7(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_,_), C2=snf_clause(_,T2, H2, I,_),
	unionC(H1,H2,P,H), (H=[], R=snf_clause(ex,T2,H,I,3); R=snf_clause(ex,T2,H,I,2)).
	
%SRES8
res_SRES8(C1,C2,P,R) :- C1=snf_clause(_,T1, H1,_, X1), C2=snf_clause(_,T2, H2,_,X2), (X1 > X2, N=X1; N=X2),
	unionC(H1,H2,P,H), R=snf_clause(true,T2,H,nil,N).*/

%resolution--------------------------------------------end-------------------------------------


%----------------------------------start----step_resolution-----------------------------------------

%resolution(Lp, Ln, P, L)----------------------------start-------------------------------------------
%do all the possible step-resolutions on P. （得到的结果也都包含了Lp和Ln）
loopresolution([], Ln, P, Ln).
loopresolution(L, [], _, L).
loopresolution([H|Lp], Ln, P, L) :- loopresolution_list(H, Ln, P, L1), loopresolution(Lp, Ln, P, L2), 
	append(L1, L2, R1), %trace, write("\n"), write("R***====="), write(R1), 
	append(R1, Ln, R), sort(R, L).

loopresolution_list(C, [], _, [C]).
loopresolution_list(C, [H|Ln], P, L1) :- C = snf_clause(Type1,_,_,_,_), H=snf_clause(Type2,_,_,_,_), %judgeType(C, Type1), judgeType(H, Type2), 
	(Type1 = ax, !, (Type2=ax, !, res_SRES1(C, H, P, C1); (Type2 =ex, !, res_SRES2(H, C, -P, C1); (Type2=true, !, res_SRES6(H, C, -P, C1); C1=[]))); 
		(Type1=ex, !, (Type2=ax, !, res_SRES2(C, H, P, C1); (Type2 =ex, !, res_SRES2(C, H, P, C1); (Type2=true, !, res_SRES7(H, C, -P, C1); C1=[])));
			(Type1 =true, !, (Type2=start, !, res_SRES5(C, H, P, C1); (Type2=ax, !, res_SRES6(C, H, P, C1); (Type2=ex, !, res_SRES7(C,H, P, C1); (Type2=true, !, res_SRES8(C,H,P, C1); C1=[]))));
				(Type1 =start, !, (Type2=start, !, res_SRES4(C,H, P, C1); (Type2=true, !, res_SRES5(H, C, -P, C1); C1=[])); C1 =[])
			)
		)
	),
	loopresolution_list(C, Ln, P, L2),
	(C1 =[], L1 =L2;
	append([C1], L2, L1)).
	
	

repeat_loopresolution([],_, []).
repeat_loopresolution(L, P, Res) :- sort(L, L1), all_PosC(L1, P, Lp), all_NegC(L1, P, Ln), loopresolution(Lp, Ln, P, R2), 
	rewrite(R2, R3), sort(R3, R1),
	%trace, write("\n"), write("R1====="), write(R1), 
	(L1 = R1, Res = R1;
			repeat_loopresolution(R1, P, Res)
		%, write("\n"), write("Res="), write(Res).
	).

	/*( member(snf_clause(true,[true],[- z], _,_), R1), Res=false;
		(L1 = R1, Res = R1;
			repeat_resolution(R1, P, Res)
		)%, write("\n"), write("Res="), write(Res).
	).*/


rewrite([], []).
rewrite([C1|R1], [C2| R2]) :- (C1=snf_clause(L, H, [], I,N), (L=ax; L=ex), negation(H, H1), C2 = snf_clause(true, [true], H1, nil,N); C2 = C1), rewrite(R1, R2).

%findall(X, (member(X, L1), inCst(X, Q)), L2)

%原来为repeat_resolution(L, P, Res) :- sort(L, L1), all_PosC(L, P, Lp), all_NegC(L, P, Ln), resolution(Lp, Ln, P, R1), 
%		(L1 = R1, Res = R1;
%			repeat_resolution(R1, P, Res)
%		).%, write("\n"), write("Res="), write(Res).


loopRes(L, [], L).
loopRes([], _, []).
loopRes(L, V, R) :- appearing_list(L, V, L1), 
	step_loopresolution_list(L1, V, Rf),  
	( Rf=false, !, R=false;
		((Rf =L, R1 = Rf; loopRes(Rf, V, R1)),
			( R1 = false, !, R = false; append(L, R1, X1), sort(X1, R))
		)
	).
	/*(Rf =L, R1 = Rf; step_resolution(Rf, V, R1)),
	append(L, R1, X1), sort(X1, R).*/
	%trans(X, Y1), tranI2CTL_list(Y1, R), 
	%tranSt2CTL(Y2, Y3), 
	%elim(Y2, V, Y4), 
	%sort(Y2, R).
	%, snfL2CTLF(Y5, R).


step_loopresolution_list([], _, []).
step_loopresolution_list(L, [], L).
step_loopresolution_list(L, [P|T], R) :- appearing(L, P, L1), %write("\nl"), write("L1="), write(L1),
	repeat_loopresolution(L1, P, Res), 
	%subsumeLoop(R1,R1,R1,Res),
	( Res=false, !, R = false; 
		(member(snf_clause(start,[start],[],_,_), Res), !, R =false;
			(member(snf_clause(true,[true], [],_,_), Res), !, R=false;
				(
					append(L, Res, Res1),  %write("\nl"), write("Res1="), write(Res1),
					sort(Res1, Y), %write("\nl"), write("Y="), write(Y),
					step_loopresolution_list(Y, T, Res2), %write("\nl"), write("Res2="), write(Res2),
					(Res2=false, R=false; 
						append(Y, Res2, X), %write("\nl"), write("X="), write(X),
						sort(X, R) %,write("\nl"), write("R="), write(R)
					)
				)
			)
		)
	).
	/* append(L, Res, Res1),  write("\nl"), write("Res1="), write(Res1),
	sort(Res1, Y), write("\nl"), write("Y="), write(Y),
	step_resolution_list(Y, T, Res2), write("\nl"), write("Res2="), write(Res2),
	append(Y, Res2, X), write("\nl"), write("X="), write(X),
	sort(X, R), write("\nl"), write("R="), write(R).*/
	%trans(Res, Res1),
	%elm(Res1, R).
	
	
%---------------------------------end-----step_resolution-----------------------------------------	