open stubborn_lsts as blsts

//pred test {
//	D1 and D2w and V and I and L
//	redundancy [Init]
//	all_paths_exist
//}
//
//check lsts10 { test => correctness } for 4 seq, 7 State, 9 Transition, 2 AP, 2 Action, 24 Path
//
one sig s1,s2,s3 extends State {}
one sig l,empty extends AP {}
one sig p,q extends Path {}
fact {
	succ = Init->s1 + s1->s2 + s2->s1 + Init->s3 + s3->s2
	Init.label = l
	s1.label = l
	s2.label = empty
	s3.label = empty
	q = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s3+2->s2+3->s1 }
	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2 }
	all_paths_exist
}
check { reduces_to[q._w_pre, q._w_inf, p._w_pre, p._w_inf] } for exactly 2 AP, exactly 4 State, 4 seq, exactly 5 Transition, exactly 1 Action, 18 Path
run { reduces_to[q._w_pre, q._w_inf, p._w_pre, p._w_inf] } for exactly 2 AP, exactly 4 State, 4 seq, exactly 5 Transition, exactly 1 Action, 18 Path
