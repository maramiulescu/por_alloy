open stubborn_pg as pg

pred test_correction {
	redundancy [Init]
	all s: State-Init | s.r = Action
	D1" and D2w and I and V and L and P
	all_paths_exist
}

//one sig s0, s1, s2, s3 extends State {}
//one sig a, a", b extends Action {}
//fact {
//	S_e = Init + s0 + s1
//	T = Init->a"->s0 + Init->a->s1 + s1->a->s2 + s2->a->Init + s2->b->s3 + s0->a"->s0
//	all s: State | s.label = 1
//	Init.r = a
//}

//check fix_pg { test_correction => correctness } for 3 seq, exactly 1 Even, exactly 1 Odd, 4 State, 3 Action, 6 Transition, 4 Strategy, 15 Path
//check { test_correction => correctness } for 4 seq, exactly 1 Even, exactly 1 Odd, exactly 5 State, exactly 3 Action, exactly 6 Transition, exactly 2 Strategy, exactly 24 Path
//run { test_correction } for 4 seq, exactly 1 Even, exactly 1 Odd, exactly 5 State, exactly 3 Action, exactly 6 Transition, exactly 2 Strategy, exactly 24 Path
check { test_correction => correctness } for 4 seq, exactly 1 Even, exactly 1 Odd, 5 State, 3 Action, 6 Transition, 2 Strategy, 24 Path
