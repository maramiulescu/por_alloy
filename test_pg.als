open stubborn_pg as pg

pred test {
	D1" and D2w and I and V and L
	redundancy [Init]
	all_paths_exist
}

check pg { test => correctness } for 5 seq, exactly 1 Even, exactly 1 Odd, 5 State, 4 Action, 9 Transition, 6 Strategy, 22 Path
