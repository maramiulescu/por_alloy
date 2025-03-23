open stubborn_pg as pg

pred test_correction {
	redundancy [Init]
	all s: State-Init | s.r = Action
	D1" and D2w and I and V and L and P
	all_paths_exist
}

check fix_pg { test_correction => correctness } for 3 seq, exactly 1 Even, exactly 1 Odd, 4 State, 3 Action, 6 Transition, 4 Strategy, 15 Path
