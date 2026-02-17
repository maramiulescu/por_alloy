open stubborn_lsts as lsts

pred test {
	D1 and D2w and V and I and L
	some Init.r
	some enabled[Init] - Init.r
	some enabled[Init] & Init.r
}
check lsts { test => correctness } for 5 seq, 5 State, 2 Action, 2 AP, 9 Transition, 24 Path
