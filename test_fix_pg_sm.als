open stubborn_pg as pg

pred test_correction {
	D1" and D2w and I and V and L and P
	some Init.r
	some enabled[Init] - Init.r
	some enabled[Init] & Init.r
}

check fix_pg_smaller_bounds { test_correction => correctness } for exactly 1 Even, exactly 1 Odd, 4 seq, 4 State, 3 Action, 6 Transition, 17 Path, 4 Strategy
