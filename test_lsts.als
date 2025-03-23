open stubborn_lsts as lsts

pred test {
	D1 and D2w and V and I and L
	redundancy [Init]
	all_paths_exist
}

check lsts10 { test => correctness } for 4 seq, 7 State, 9 Transition, 2 AP, 2 Action, 24 Path

