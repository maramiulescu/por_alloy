open ample_lks as lks

pred test {
	all_paths_exist
}

check lks { test => correctness } for 4 State, 3 Transition, 1 AP, 2 Action, 8 Path
