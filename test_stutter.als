open stubborn_lsts as blsts

// "unit tests" for stutter equivalence
//	t1-t9: case (s p, t p) -> (s, p t)
//	t10: case (s t*k, t) -> (s, t)
//	t11-t13: deadlocking paths
//	t14: the one that started it all
// 
//	t1:
//	t2: corner case: when the stutter happens at the start of the cycle
//	t3: corner case: when the stutter happens in pre, right where pre ends and the cycle begins
//	t4:
//	t5: corner case: when the stutter happens at the end of the cycle
//	t6: corner case: when the stutter happens at the start of the cycle, twice
//	t7: corner case: when the stutter happens at the end of the cycle, twice
//	t8: corner case: when the stutter happens in pre, right where pre ends and the cycle begins, twice
//	t9: corner case for the corner case (t7): when the stutter happens in the cycle, in all states of the cycle
//	t10: 
//
// comment out all tests except the one to run
//
//one sig s1,s2,s3,s4,s5,s6 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t1 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s4+s4->s5+s5->s6+s6->s4
//	Init.label = empty
//	s1.label = l
//	s2.label = empty
//	s3.label = l
//	s4.label = empty
//	s5.label = empty
//	s6.label = l
//	p = { path: Path | path.start = Init and path.end = s4 and path.tr.src = 0->Init+1->s1+2->s2+3->s3+4->s4+5->s5+6->s6 }
//}
//pred c1 {
//	p.w_pre = 0->empty+1->l+2->empty+3->l
//	p.w_inf = 0->empty+1->l
//}
//check lasso_7states { t1 => c1}  for 2 AP, 7 State, 7 Transition, 7 seq, 1 Action, 1 Path
//run { t1 } for 2 AP, 7 State, 7 Transition, 7 seq, 1 Action, 1 Path
//
//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t2 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s1
//	Init.label = empty
//	s1.label = l
//	s2.label = l
//	s3.label = empty
//	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
//}
//pred c2 {
//	p.w_pre = 0->empty
//	p.w_inf = 0->l+1->empty
//}
//check lasso_4states_0 { t2 => c2 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//run { t2 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//
//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t3 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s2
//	Init.label = empty
//	s1.label = l
//	s2.label = l
//	s3.label = empty
//	p = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
//}
//pred c3 {
//	p.w_pre = 0->empty
//	p.w_inf = 0->l+1->empty
//}
//check lasso_4states_1 { t3 => c3 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//run { t3 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
////
//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t4 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s2
//	Init.label = empty
//	s1.label = l
//	s2.label = empty
//	s3.label = l
//	p = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
//}
//pred c4 {
//	p.w_pre = 0->empty+1->l
//	p.w_inf = 0->empty+1->l
//}
//check lasso_4states_2 { t4 => c4 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//run { t4 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path

//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t5 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s1
//	Init.label = empty
//	s1.label = l
//	s2.label = empty
//	s3.label = l
//	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
//}
//pred c5 {
//	p.w_pre = 0->empty
//	p.w_inf = 0->l+1->empty
//}
//check lasso_4states_3 { t5 => c5 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//run { t5 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//
//one sig s1,s2,s3,s4 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t6 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s4+s4->s1
//	Init.label = empty
//	s1.label = l
//	s2.label = l
//	s3.label = l
//	s4.label = empty
//	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2+3->s3+4->s4 }
//}
//pred c6 {
//	p.w_pre = 0->empty
//	p.w_inf = 0->l+1->empty
//}
//check lasso_5states_0 { t6 => c6 } for 2 AP, 5 State, 5 Transition, 5 seq, 1 Action, 1 Path
//run { t6 } for 2 AP, 5 State, 5 Transition, 5 seq, 1 Action, 1 Path
//
//one sig s1,s2,s3,s4 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t7 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s4+s4->s1
//	Init.label = empty
//	s1.label = l
//	s2.label = empty
//	s3.label = l
//	s4.label = l
//	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2+3->s3+4->s4 }
//}
//pred c7 {
//	p.w_pre = 0->empty
//	p.w_inf = 0->l+1->empty
//}
//check lasso_5states_1 { t7 => c7 } for 2 AP, 5 State, 5 Transition, 5 seq, 1 Action, 1 Path
//run { t7 } for 2 AP, 5 State, 5 Transition, 5 seq, 1 Action, 1 Path
// 
//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t8 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s2
//	Init.label = empty
//	s1.label = empty
//	s2.label = empty
//	s3.label = l
//	p = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
//}
//pred c8 {
//	no p.w_pre
//	p.w_inf = 0->empty+1->l
//}
//check lasso_4states_3 { t8 => c8 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//run { t8 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//
//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t9 {
//	succ = Init->s1+s1->s2+s2->s3+s3->s1
//	Init.label = empty
//	s1.label = l
//	s2.label = l
//	s3.label = l
//	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
//}
//pred c9 {
//	p.w_pre = 0->empty
//	p.w_inf = 0->l
//}
//check lasso_4states_4 { t9 => c9 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//run { t9 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 1 Path
//
// one sig s1,s2,s3 extends State {}
// one sig l,empty extends AP {}
// one sig p,q extends Path {}
// pred t10 {
// 	succ = Init->s1+s1->s2+s2->s3+s3->s2
// 	Init.label = empty
// 	s1.label = l
// 	s2.label = empty
// 	s3.label = l
// 	p = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s1+2->s2+3->s3 }
// 	q = { path: Path | path.start = s2 and path.end = s2 and path.tr.src = 0->s2+1->s3 }
// }
// pred c10 {
// 	p.w_pre = 0->empty+1->l
// 	p.w_inf = p.w_pre
// 	no q.w_pre
// 	q.w_inf = 0->empty+1->l
// 	reduces_to[p,q]
// }
// check lasso_4states_5 { t10 => c10 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path
// run { t10 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path

//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p,q extends Path {}
//pred t11 {
//	succ = Init->s1+s1->s2+s2->s3
//	Init.label = empty
//	s1.label = l
//	s2.label = empty
//	s3.label = l
//	p = { path: Path | path.start = Init and path.end = s3 and path.tr.src = 0->Init+1->s1+2->s2 }
//	q = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init }
//}
//pred c11 {
//	p.w_pre = 0->empty+1->l+2->empty+3->l
//	no p.w_inf
//	q.w_pre = 0->empty+1->l
//	not reduces_to[p,q]
//	not stutter_eq[p,q]
//	not stutter_eq[q,p]
//}
//check deadlocking_4states_0 { t11 => c11 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path
//run { t11 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path
//
//one sig s1,s2,s3 extends State {}
//one sig l,empty extends AP {}
//one sig p extends Path {}
//pred t12 {
//	succ = Init->s1+s1->s2+s2->s3
//	Init.label = empty
//	s1.label = empty
//	s2.label = l
//	s3.label = l
//	p = { path: Path | path.start = Init and path.end = s3 and path.tr.src = 0->Init+1->s1+2->s2 }
//}
//pred c12 {
//	p.w_pre = 0->empty+1->l
//	no p.w_inf
//}
//check deadlocking_4states_1 { t12 => c12 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path
//run { t12 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path
//
 //one sig s1,s2,s3 extends State {}
// one sig l,empty extends AP {}
// one sig p,q extends Path {}
// pred t13 {
// 	succ = Init->s1+s1->s2+s2->s3
// 	Init.label = l
// 	s1.label = l
// 	s2.label = l
// 	s3.label = l
// 	p = { path: Path | path.start = Init and path.end = s3 and path.tr.src = 0->Init+1->s1+2->s2 }
// 	q = { path: Path | path.start = Init and path.end = Init }
// }
// pred c13 {
// 	p.w_pre = 0->l
// 	no p.w_inf
// 	stutter_eq[p,q]
// 	stutter_eq[q,p]
// }
// check deadlocking_4states_2 { t13 => c13 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path
// run { t13 } for 2 AP, 4 State, 4 Transition, 4 seq, 1 Action, 2 Path

one sig s1,s2,s3 extends State {}
one sig l,empty extends AP {}
one sig p,q extends Path {}
pred t14 {
	succ = Init->s1 + s1->s2 + s2->s1 + Init->s3 + s3->s2
	Init.label = l
	s1.label = l
	s2.label = empty
	s3.label = empty
	q = { path: Path | path.start = Init and path.end = s2 and path.tr.src = 0->Init+1->s3+2->s2+3->s1 }
	p = { path: Path | path.start = Init and path.end = s1 and path.tr.src = 0->Init+1->s1+2->s2 }
	all_paths_exist
}
pred c14 {
	reduces_to[q,p]
	stutter_eq[p,q]
	stutter_eq[p,q]
}
check { t14 => c14 } for exactly 2 AP, exactly 4 State, 4 seq, exactly 5 Transition, exactly 1 Action, 18 Path
run { t14 } for exactly 2 AP, exactly 4 State, 4 seq, exactly 5 Transition, exactly 1 Action, 18 Path
