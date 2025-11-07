open stubborn_rg as rg

pred test_correction {
	I and W and R and G1 and G2 and S and D and V
	redundancy [Init]
	all_paths_exist
}

check fix_rg { test_correction => correctness } for 4 seq, 5 State, 5 Transition, 2 Action, exactly 3 Label, 14 Path, 1 Strategy
check fix_rg_higher_bounds { test_correction => correctness } for 5 seq, 5 State, 4 Action, 3 Label, 9 Transition, 6 Strategy, 26 Path
