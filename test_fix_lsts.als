open stubborn_lsts as blsts

pred test_correction {
	D1" and D2w and V and I and L
	all_paths_exist
}

check fix_lsts { test_correction => correctness } for 5 seq, 5 State, 2 Action, 2 AP, 9 Transition, 24 Path
