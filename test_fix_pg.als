open stubborn_pg as pg

pred test_correction {
	redundancy [Init]
	D1" and D2w and I and V and L and P
	all_paths_exist
}

check fix_pg_original_bounds { test_correction => correctness } for 5 seq, exactly 1 Even, exactly 1 Odd, 5 State, 4 Action, 9 Transition, 6 Strategy, 26 Path
check fix_pg_smaller_bounds { test_correction => correctness } for exactly 1 Even, exactly 1 Odd, 4 seq, 4 State, 3 Action, 6 Transition, 17 Path, 4 Strategy