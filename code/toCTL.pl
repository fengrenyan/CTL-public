

:- module(toCTL, [toCTL/4]).


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