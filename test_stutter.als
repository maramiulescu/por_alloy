open stubborn_lsts as blsts

// "unit tests" for stutter equivalence
// comment out all tests except the one to run

one sig s1,s2,s3,s4,s5,s6 extends State {}
one sig l,empty extends AP {}
one sig p extends Path {}
pred t1 {
	succ = Init->s1+s1->s2+s2->s3+s3->s4+s4->s5+s5->s6+s6->s4
	Init.label = empty
	s1.label = l
	s2.label = empty
	s3.label = l
	s4.label = empty
	s5.label = empty
	s6.label = l
	p = { path: Path | path.start = Init and path.end = s4 and path.tr.src = 0->Init+1->s1+2->s2+3->s3+4->s4+5->s5+6->s6 }
}
pred c1 {
	p._w_pre = 0->empty+1->l+2->empty+3->l
	p._w_inf = 0->empty+1->l
}
check lasso_7states { t1 => c1}  for 2 AP, 7 State, 7 Transition, 7 seq, 1 Action, 1 Path
run { t1 } for 2 AP, 7 State, 7 Transition, 7 seq, 1 Action, 1 Path

one sig s1,s2,s3 extends State {}
one sig l,empty extends AP {}
one sig p extends Path {}
pred t2 {
	succ = Init->s1+s1->s2+s2->s3+s3->s1
	Init.label = empty
	s1.label = l
	s2.label = l
	s3.label = empty
	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
}
pred c2 {
	p._w_pre = 0->empty
	p._w_inf = 0->l+1->empty
}
check lasso_4states_0 { t2 => c2 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
run { t2 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path

one sig s1,s2,s3 extends State {}
one sig l,empty extends AP {}
one sig p extends Path {}
pred t3 {
	succ = Init->s1+s1->s2+s2->s3+s3->s2
	Init.label = empty
	s1.label = l
	s2.label = l
	s3.label = empty
	p = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
}
pred c3 {
	p._w_pre = 0->empty
	p._w_inf = 0->l+1->empty
}
check lasso_4states_1 { t3 => c3 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
run { t3 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path

one sig s1,s2,s3 extends State {}
one sig l,empty extends AP {}
one sig p extends Path {}
pred t4 {
	succ = Init->s1+s1->s2+s2->s3+s3->s2
	Init.label = empty
	s1.label = l
	s2.label = empty
	s3.label = l
	p = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
}
pred c4 {
	p._w_pre = 0->empty+1->l
	p._w_inf = 0->empty+1->l
}
check lasso_4states_2 { t4 => c4 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
run { t4 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
