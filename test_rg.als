open stubborn_rg as rg

pred test {
	I and W and R and G1 and G2 and S and C and D
	some Init.r
	some enabled[Init] - Init.r
	some enabled[Init] & Init.r
}

check rg { test => correctness } for 4 seq, 4 State, 4 Transition, 2 Action, exactly 3 Label, 10 Path, 1 Strategy