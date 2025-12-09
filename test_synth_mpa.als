open ample_synth_mpa as mpa

pred test {
	A1 and A2 and A3 and A51 and A52
//	redundancy [Init]
	all_paths_exist
}

run rg { test } for 4 seq, 4 State, 4 Transition, 3 Action, exactly 3 Label, 14 Path, 2 Strategy
//check rg { test => correctness } for 4 seq, 4 State, 4 Transition, 2 Action, exactly 3 Label, 10 Path, 1 Strategy
