
%The Instantiation Process
:- module(instantiate, [instante/5,insAllL/4]).

%:- dynamic(pair/2).
%:- dynamic(prop/1).


insAllL([], _, _, _). %该函数用于找到所有的实例化公式。（遍历）
insAllL([H|L], V, V1, V2) :- H = snf_clause(Type, Q, T, I), %V1为新引入的变量的集合，V2为能被实例化的变量的集合.
	(Type = true, true_ins([H], V, V1, V2, R1);
		temp_ins([H], V, V1, V2, R1)
	), insAllL(L, V, V1, V2).

%pair(p, L), append([c], L, L1), assert(pair(p, L1)), retractall(pair(p, L)).

/*初始时，V2=[]，表示V1中还没有原子被实例化. 该函数保证找到实例化的公式（如果有）。当所有V1中的原子都被实例化后结束。
该过程主要分为三部分：（1）对true子句中变量的实例化；（2）对时序字句中变量的实例化；（3）寻找传递类型的字句集并做实例化。
*/
instante([], _, _, _,[]). 
instante(L, V, V1, V2, R) :- obtainAllTrue(L, L1), true_ins(L1, V, V1, V2, R1), subtract(L, L1, L2),
	subtract(V1, R1, V3),
	(V3=[], R = V1;
		temp_ins(L2, V, V3, R1, R2), subtract(V3, R2, V4), 
		(V4 =[], R = V1;
			append(R1, R2, V5), tran_ins(L2, L, V, V4, V5, R3), subtract(V4, R3, V6),
			(V6=[], R=V1;
				append(V5, R3, V7), 
				(V7=V2, R = V7;
					instante(L, V, V6, V7, R4), append(V7, R4, R)
				)
			)
		)
	).
	

tran_ins([],_, _, _,_, []). %寻找具有传递性的实例化关系。
tran_ins([C|L1], L, V, V1, V2, R) :- C = snf_clause(Type, H, T, I), subtract(V1, V2, V3), 
	(subset(H, V1),  append(V, V3, V4), obtainAtom(T, H1), 
		(intersection(H1, V4, []), !, obtainTandStart(L, V1, L2), findProp(L2, L2, H,X),
			(X=[], C1=[];
				(pair(X, Y), append([(Type,T,I)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y))), C1= []; 
					(T=[], !, C1= []; assert(pair(X, [(Type,T,I)])), C1= X)
				)
			); C1 =[]
		); C1 =[]
	),
	(C1 =[], V5=V2; append([C1], V2, V5)), %subtract(V1, [C1], V2),
	tran_ins(L1, L, V, V1, V5, R1),
	(C1=[], R = R1; append([C1], R1, R)).


findProp([], _,_, []).
findProp([C|L], L1, H, X) :- (C =snf_clause(true, [Y], T1, nil),
	findall(T, (C1=snf_clause(true, [Y], [T], nil), member(C1, L1)), L2); 
		%(subset(H, L2), X = Y; findProp(L, L1, H, X));
		C =snf_clause(start, [Y], T1, nil), findall(T, (C1=snf_clause(start, [Y], [T], nil), member(C1, L1)), L2)
		%(subset(H, L2), X = Y; 
	), (subset(H, L2), X = Y; findProp(L, L1, H, X)).


obtainTandStart([], _,[]).
obtainTandStart([C|L], V1, R) :- C = snf_clause(Type, H, T, I), 
	(Type = true, ((member(- X, T), member(X,V1), subtract(T, [- X], H1)), !, C1= snf_clause(true, [X], H1, nil); C1 =[]); 
		(Type = start, C1 = C; C1 = [])
	), 
	obtainTandStart(L, V1, L1),
	(C1=[], R = L1; append([C1], L1, R)).
	
	
	
%temp_ins(_,_,[],_,[]).
temp_ins([], _, _,_, []).%该过程实例化头为时序公式的子句，具体过程类似于true_ins过程
temp_ins([C|L1], V, V1, V2, R) :- C = snf_clause(Type, H, T, I), subtract(V1, V2, V3),  
	( H = [X], !, 
		(member(X, V1), !, append(V, V3, V4), obtainAtom(T, H1), 
			(intersection(H1, V4, []), !, 
				(pair(X, Y), (T = [], !; append([(Type,T,I)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y)))), C1= []; 
					(T=[], !, C1= []; assert(pair(X, [(Type,T,I)])), C1= X)
				);
				C1=[]
			); C1=[]
		); C1=[]
	), 
	(C1 =[], V5=V2; append([C1], V2, V5)), %subtract(V1, [C1], V2),
	temp_ins(L1, V, V1, V5, R1),
	(C1=[], R = R1; append([C1], R1, R)).


%true_ins(_,_,[],_,[]).
true_ins([], _, _,_, []). 
/*true_ins([C|L1], V, V1, V2, R) :- C = snf_clause(_, H, T, nil), obtainAtom(T, H1), intersection(H1, V1, L3), subtract(L3, V2, L), length(L, N), 
(intersection(H1, V, L2), L2=[],
	(N >1, C1=[]; 
		(N =1, !, L = [X], 
			(member(- X, T), !, delete(T, - X, H2), 
				(pair(X, Y), (H2 = [], !; append([(true, H2, nil)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y)))), C1= []; 
					(H2=[], !, C1= []; assert(pair(X, [(true, H2, nil)])), C1= X)
				);
				C1=[]
			);
			C1= []
		)
	);
	C1 =[]
), 
	(C1 =[], V3=V2; append([C1], V2, V3)), %subtract(V1, [C1], V2),
	true_ins(L1, V, V1, V3, R1),
	(C1=[], R = R1; append([C1], R1, R)).*/
	
true_ins([C|L1], V, V1, V2, R) :- C = snf_clause(_, H, T, nil), obtainAtom(T, H1), intersection(H1, V1, L3), subtract(L3, V2, L), length(L, N), 
(L =[], findall(X,(member(- X, T), member(X, V1)), LL), true_list(LL, T), C1=[]; 
		/*(member(- X, T), !, delete(T, - X, H2), %H2=[]时，表示X->false,也即是X被false实例化，也是需要添加的。2020-4-18
				(pair(X, Y), append([(true, H2, nil)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y))), C1= []; 
					assert(pair(X, [(true, H2, nil)])), C1= X
				);
				C1=[]
		);*/ %2020-4-19增加
	(intersection(H1, V, L2), L2=[],
		(N >1, C1=[]; 
			(N =1, !, L = [X], 
				(member(- X, T), !, delete(T, - X, H2), %H2=[]时，表示X->false,也即是X被false实例化，也是需要添加的。2020-4-18
					(pair(X, Y), append([(true, H2, nil)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y))), C1= []; 
						assert(pair(X, [(true, H2, nil)])), C1= X
					);
					C1=[]
				);
				C1= []
			)
		);
		C1 =[]
	)
), 
	(C1 =[], V3=V2; append([C1], V2, V3)), %subtract(V1, [C1], V2),
	true_ins(L1, V, V1, V3, R1),
	(C1=[], R = R1; append([C1], R1, R)).
	
/*true_ins([C|L1], V, V1, V2, R) :- C = snf_clause(_, H, T, nil), obtainAtom(T, H1), intersection(H1, V1, L3), subtract(L3, V2, L), length(L, N), 
	(intersection(H1, V, L2), L2=[],
		(N >1, C1=[]; 
			(N =1, !, L = [X], 
				(member(- X, T), !, delete(T, - X, H2), %H2=[]时，表示X->false,也即是X被false实例化，也是需要添加的。2020-4-18
					(pair(X, Y), append([(true, H2, nil)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y))), C1= []; 
						assert(pair(X, [(true, H2, nil)])), C1= X
					);
					C1=[]
				);
				C1= []
			)
		);
		C1 =[]
	), 
	(C1 =[], V3=V2; append([C1], V2, V3)), %subtract(V1, [C1], V2),
	true_ins(L1, V, V1, V3, R1),
	(C1=[], R = R1; append([C1], R1, R)).*/


%将true子句中出现的V1中的变量的所有可能的实例化都找出来，例snf_clause(true, [true], [- x1, -x2, a], nil)中，只要
%x2或x1被实例化了，则x2和x1同能被实例化，有pair(x1, [(true, x2,a)]), pair(x2, [(true, x1,a)]).
true_list([],_). 
true_list([X|L], T) :- delete(T, - X, H2), %H2=[]时，表示X->false,也即是X被false实例化，也是需要添加的。2020-4-18
	(pair(X, Y), append([(true, H2, nil)], Y, Y2), sort(Y2, Y1), assert(pair(X, Y1)), (Y1=Y,!; retractall(pair(X, Y))); 
		assert(pair(X, [(true, H2, nil)]))
	).


%获取所有的true子句
obtainAllTrue([], []). 
obtainAllTrue([C|L], R) :- C = snf_clause(Type, H, T, X), 
	(Type = true, C1 = C; C1 = []), 
	obtainAllTrue(L, L1),
	(C1=[], R = L1; append([C1], L1, R)).