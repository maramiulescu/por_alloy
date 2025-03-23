open stubborn_rg as rg

pred test_correction {
	I and W and R and G1 and G2 and S and D and V
	redundancy [Init]
	all_paths_exist
}

check fix_rg { test_correction => correctness } for 4 seq, 5 State, 5 Transition, 2 Action, exactly 3 Label, 14 Path, 1 Strategy
