open stubborn_lsts as lsts

pred test {
	D1 and D2w and V and L
	not I
	all_paths_exist
}

run { test } for exactly 2 S, exactly 3 T, exactly 2 A, exactly 6 Path, exactly 2 AP
