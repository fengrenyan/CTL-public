

:- module(tempRes, [temp_resolution/8]).

%:- use_module(loopRes).


temp_resolution([], _,_,_,[],[],[], V).
temp_resolution(TL, _, [],_, [], TL, [], V).
temp_resolution(TL, _, _, [], [], TL, [], V).
temp_resolution([H|TL], [X|L], L1, [Y|V], R, TL1, W, V1) :- temp_resolution_list(H, L1, [Y|V], R1,X, V1), 
	temp_resolution(TL, L, L1, [Y|V], R2, TL2, W1, V1),
	(R1 = [], append([H], TL2, TL1), W = W1, R=R2; TL1= TL2,  append([X], W1, W), append(R1, R2, R)).
	
	
	
temp_resolution_list(_, _, [], [], _, V).
temp_resolution_list(H, L, [Y|V], R,W, V1):- H = snf_clause(Type, Hs, Ts, I), 
	(Type = af, (posC(Y, H), fA(H, L, Y, R,W, V1); (negC(Y, H),fA(H, L, - Y, R,W, V1); temp_resolution_list(H, L, V, R,W, V1)));
		(Type = ef, (posC(Y, H), fE(H, L, Y, R,W, V1); (negC(Y, H),fE(H, L, - Y, R,W, V1); temp_resolution_list(H, L, V, R,W, V1))))
	).
	
fA(C, L, Y, R,W, V) :- find_Asometime_clauses(L, L1), loopFormula(L1, Y, V, [[Y]], F),  %write("\n F===="), write(F),write("\n"),
	C = snf_clause(Type, Q, H, I),
	((F = false; F=[]), R = []; snfres(F, Y, Q, R, W), write("\n ERES1===="), write(R), write("\n")).
	
snfres(true, Y,Q, R, W) :- negation(Q, T1), append(T1, [Y], T2), append(T2, [W], T3), 
	R = [snf_clause(ax,[W],[Y],nil), snf_clause(true,[true], T2,nil), snf_clause(true,[true], T3,nil), snf_clause(ax,[W], [Y, W],nil)].
snfres(F, Y, Q, R, W) :-  equall(Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), cirRes(W, P, T1, F, R1),
	L1= [snf_clause(true,[true], T3,nil), snf_clause(ax,[W], [P, W],nil)], append(R1, L1, R).

cirRes(_,_, _, [], []).
cirRes(W, P, Q, [F|T], L) :- negation(F, F1), append([P], F, X1), append(Q, X1, F2), %2020-4-9append([P], F1, X1)变成append([P], F, X1)
	C1 = snf_clause(ax,[W], X1,nil), C2 = snf_clause(true,[true], F2, nil),
	cirRes(W,P,Q, T, L1),
	append([C1], L1, L2), append([C2], L2, L3), sort(L3, L).


fE(C, L, Y, R,W, V) :- %C= exist_future_clause(Q, H, I), find_Esometime_loop(L, Y, F, I), 
	find_Esometime_clauses(L, Ind, L1), loopFormula(L1, Y, V, [[Y]], F), %write("\n F===="), write(F),write("\n"),
	C = snf_clause(Type, Q, H, I), 
	((F = false; F=[]), R = []; snfresE(F, Y, Q, R, W,I), write("\n ERES2===="), write(R), write("\n")).
	
snfresE(true, Y,Q, R, W,I) :- equall(Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), 
	R = [snf_clause(ex,[W],[Y],I), snf_clause(true,[true], T2,nil), snf_clause(true,[true], T3,nil), snf_clause(ex, [W], [P, W],I)].
snfresE(F, Y, Q, R, W,I) :-  equall(Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), 
	cirResE(W, P, T1, F, R1,I),
	L1= [snf_clause(true,[true], T3, nil), snf_clause(ex,[W], [P, W],I)], append(R1, L1, R).

cirResE(_,_, _, [], [],I).
cirResE(W, P, Q, [F|T], L,I) :- negation(F, F1), append([P], F, X1), append(Q, X1, F2), 
	C1 = snf_clause(ex, [W], X1,I), C2 = snf_clause(true,[true], F2, nil),
	cirResE(W,P,Q, T, L1,I),
	append([C1], L1, L2), append([C2], L2, L3), sort(L3, L).