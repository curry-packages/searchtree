% Implementation of Control.AllSolutions.getOneSolution:

:- block prim_getOneSolution(?,?,-,?).
prim_getOneSolution(G,partcall(1,prim_getOneSolutionWorld,[G]),
		    E,E).

:- block prim_getOneSolutionWorld(?,?,?,-,?).
prim_getOneSolutionWorld(RSG,_,Sol,E0,E) :-
	hnfAndWaitUntilGround(RSG,SG,E0,E1),
	prim_getOneSol_exec(SG,Sol,E1,E).

:- block prim_getOneSol_exec(?,?,-,?).
prim_getOneSol_exec(SG,Sol,E0,E) :-
	hasPrintedFailure
	 -> prim_getOneSolWithPF(SG,Sol,E0,E)
	  ; asserta(hasPrintedFailure),
	    prim_getOneSolWithoutPF(SG,Sol,E0,E).

prim_getOneSolWithPF(SG,Sol,E0,E) :-
	prim_apply(SG,X,'Prelude.True',E0,E1), !,
	Sol='$io'('Prelude.Just'(X)), E1=E.
prim_getOneSolWithPF(_,'$io'('Prelude.Nothing'),E,E).

prim_getOneSolWithoutPF(SG,Sol,E0,E) :-
	prim_apply(SG,X,'Prelude.True',E0,E1), retract(hasPrintedFailure), !,
	Sol='$io'('Prelude.Just'(X)), E1=E.
prim_getOneSolWithoutPF(_,'$io'('Prelude.Nothing'),E0,E) :-
	retract(hasPrintedFailure), E0=E.

