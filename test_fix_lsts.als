open stubborn_lsts as blsts

pred test_correction {
	D1" and D2w and V and I and L
	all_paths_exist
}
check fix_lsts { test_correction => correctness } for 4 seq, 6 State, 6 Transition, 2 AP, 2 Action, 18 Path
