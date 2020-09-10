
%replacing Process: 找到匹配trans规则中的字句的集合，用左边替代这个集合，并酌情将该子句集中的部分或全部子句删除。

:- module(replaceTrans, [re2CTL/2,re2CTL_until/1]).



/*引入formula(X,Y)对，其定义为：
（1）for each pair(X,Y), there is formula(X,Y);
（2）后面每成功调用一个re2CTL有一个formula对被添加。

该过程是一个从底向上的递归过程，最底部对应的是SNF子句，随着re2CTL规则的调用得到的公式不再是SNF子句。
新引入的变量也呈一种从底向上的方式被公式化。例如，如果新变量被引入的顺序为<x1, ..., xn>，则xi被公式化的顺序为<xn, ..., x1>。


注意：如果x为端点变量（如上例中的xn），则在替换过程中不要带有时序词的公式（除非没有命题公式），因为会被化简掉。例：
 （1）until: F =  (~((a & b) $ (c \/ d))), ctlForget(F, [a], R), write("\n ========"), write(R).
 
 listing(formula).:- dynamic formula/3. %/

formula(snf, x1, [ (true, [c, d], nil)]).
formula(snf, z, [ (af, [x1], nil), (true, [b, c, d], nil), (true, [b, x1], nil), (true, [c, d, x2], nil), (true, [x1, x2], nil)]).
formula(au, z, [ ([x2], [x1], nil)]).
formula(snf, x2, [ (ax, [b, c, d], nil), (ax, [b, x1], nil), (ax, [c, d, x2], nil), (true, [b], nil)]). 

在本例中，x1和x2都为端点变量，既在trans过程中x1和x2的后面都没有指向新的变量了。
显然x1被替换为c \/ d，这样(ax, [b, x1], nil) = (ax, [b, c, d], nil) 并且被(true, [b], nil)包蕴，因此被削去。
此时，剩下[(ax, [c, d, x2], nil), (true, [b], nil)], 通过until和instantiate过程的定义，显然(ax, [c, d, x2], nil)被移除。
*/






%%%re2CTL规则，对应trans的逆过程，其中V是被遗忘的原子命题的集合。

%Trans(3)
re2CTL_con(V) :- findall([Q, L1], formula(snf, Q, L1), R),
	(R =[], !; con_list(R)).
	
onlyTrue([]).
onlyTrue([H|T]) :- H = (true, L1, Type), onlyTrue(T).

con_list([]).
con_list([H|T]) :- H = [Q, L1],  assert(formula(con, Q, L1)), con_list(T).

%Trans(4):好像不需要，因为trans过程最终得到的都是文字的吸取
/*re2CTL(V) :- findall([Q, P, X], (formula(T1, Q, L1), (not(member(P, V)); formula(T2, P, LP)), 
	(not(member(X, V)); formula(T3, X, LX)),
	(L1=[(true, [X, P], nil)]; L1=[(true, [P, X], nil)])), R),
	(R =[], !; dis_list(R)).
	
dis_list([]).
dis_list([H|T]) :- H = [Q, P, X],  assert(formula(dis, Q, [([X], [P])])), dis_list(T).*/


%Trans(7)
re2CTL_future(V) :- findall([Q, P, L1, L2, Type, I], (formula(snf, Q, L1), formula(snf, P, L2), member((Type, [P], I), L1)), R), !,
	(R=[], !; future_list(R)).
	
future_list([]).
future_list([H|T]) :- H = [Q, P, L1, L2, Type,I], 
	((Type=ef; Type=af), subtract(L1, [(Type, [P], I)], L11), retractall(formula(snf, Q, L1)), (L11=[], !; assert(formula(snf, Q, L11))); !), %2020-5-2add
	(Type = ef, !, assert(formula(ef, Q, [([P], I)]));
		(Type = af, !, assert(formula(af, Q, [([P], I)])); !)
	), future_list(T).


%Trans(6)
re2CTL_next(V) :- findall([Q, P, L1, L2, Type, I], (formula(snf, Q, L1), formula(snf, P, L2), member((Type, [P], I), L1)), R), !,
	(R=[], !; next_list(R)).
	
next_list([]).
next_list([H|T]) :- H = [Q, P, L1, L2, Type,I], 
	((Type=ex; Type=ax), subtract(L1, [(Type, [P], I)], L11), retractall(formula(snf, Q, L1)), (L11=[], !; assert(formula(snf, Q, L11))); !), %2020-5-2add
	(Type = ex, !, assert(formula(ex, Q, [([P], I)]));
		(Type = ax, !, assert(formula(ax, Q, [([P], I)])); !)
	), next_list(T).



%Trans(10)
re2CTL_global(V) :- findall([Q, P, L1, L2], (formula(snf, Q, L1), formula(snf, P, L2), member((true, [P], nil), L1)), R), !,
	(R=[], !; global_list(R)).
	
global_list([]).
global_list([H|T]) :- H=[Q,P,L1,L2], 
	(member((ex, [P], I), L2), !, assert(formula(eg, Q, [([P], I)])), delete(L2, (ex, [P], I), L3), 
		retractall(formula(snf, P, L2)), assert(formula(snf, P, L3));
		(member((ax, [P], I), L2), !, assert(formula(ag, Q, [([P], I)])), delete(L2, (ax, [P], I), L3), 
			retractall(formula(snf, P, L2)), assert(formula(snf, P, L3)); !
		)
	),global_list(T).
	

%Trans(11) and (8)
re2CTL_until(V) :- findall([Q,P, L, L1, L2], (formula(snf, Q, L1), member((true, [L, P], nil), L1), formula(snf, P, L2), 
	(not(member(L, V)); formula(snf, [L], LL))), R), !,
	(R=[], !; until_list(R)).
/*(R=[], !; 
	(member((ex, [L, P], I), L2), !, 
		(member((ef, [L], I), L1), assert(formula(eu, [Q], [([P], [L], I)])), delete(L2, (ex, [L], I), L3), 
			retractall(formula(snf, [P], L2)), assert(formula(snf, [P], L3)); !);
		(member((ax, [L, P], nil), L2), !, (member((af, [L], nil), L1), assert(formula(au, [Q], [([P], [L], nil)])), 
			delete(L2, (ax, [L], nil), L3), retractall(formula(snf, [P], L2)), assert(formula(snf, [P], L3)); !); !
		)
	)
).*/

until_list([]).
until_list([H|T]) :- H = [Q,P, L, L1, L2],
	(member((ex, [L, P], I), L2), !, 
		(member((ef, [L], I), L1), assert(formula(eu, Q, [([P], [L], I)])), delete(L2, (ex, [L,P], I), L3), 
			retractall(formula(snf, P, L2)), assert(formula(snf, P, L3)); !);
		(member((ax, [L, P], nil), L2), !, (member((af, [L], nil), L1), assert(formula(au, Q, [([P], [L], nil)])), 
			delete(L2, (ax, [L,P], nil), L3), retractall(formula(snf, P, L2)), assert(formula(snf, P, L3)); !); !
		)
	), until_list(T).



%一个过程调用re2CTL_XX规则。

re2CTL(V, R) :- re2CTL_until(V), re2CTL_global(V), re2CTL_future(V), re2CTL_next(V), re2CTL_con(V),
	obtainF(R1), write("\n **************\nformula:"), write(R1), write("\n **************\n"), deleteTemp(R1, R), 
	write("\n #################\n CTL formula:"), write(R), write("\n #################\n").
	
obtainF(R) :- findall(formula(X, Y,Z), formula(X, Y,Z), F), sort(F, R).

deleteTemp([], []).
deleteTemp([H|T], R) :- H = formula(Type, Q, L1), 
	(Type=con, !, H1=H; %(member((true, X, I), L1), temp_list(L1, L2); L2=L1), H1=formula(con, Q, L2), deleteTemp(T, T1); 
		(Type=snf, H1=[]; H1=H)
	),
	deleteTemp(T, R1),
	(H1=[], R= R1; append([H1], R1, R)).

temp_list([], []).
temp_list([H|T], R) :- H = (Type, Q, I), 
	((Type=true; Type=start), C =H; C = []),
	temp_list(T, R1),
	(C=[], R=R1; append([C], R1, R)).


