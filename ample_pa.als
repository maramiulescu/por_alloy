module ample_pa

open lib/lsts[Sigma,Action] as lsts

--------- finite state program 
sig Q {
	label: one Sigma,
	enabled_Q: set Operation,
	T_Q: enabled_Q -> one Q,
	ample: S -> set Operation
}{
	all s: S | s.ample in enabled_Q
}
one sig Qinit extends Q {}
sig Operation {}

--------- Buchi automaton
sig Sigma {}
sig S {
	enabled_S: set Sigma,
	T_S: enabled_S -> S
}
one sig Sinit extends S {}
sig Accepting in S {}

--------- product automaton 
sig Action {
	plabel: one Operation,
	blabel: one Sigma
}
sig State extends AState {
	pstate: one Q,
	bstate: one S
}{
	r = amp[pstate,bstate]
}
one sig Init extends State {}{
	pstate = Qinit and bstate = Sinit
}

fact { 
	rooted_at [Init]
	valid_product_transitions
	all_product_transitions_exist
	all disj s,s": State | !(s.pstate=s".pstate and s.bstate=s".bstate)
	all disj a,a": Action | !(a.plabel=a".plabel and a.blabel=a".blabel)
	let r = { q,q": Q | some op: Operation | q->op->q" in T_Q } | Qinit.*r = Q
}

pred valid_product_transitions {
	all t: Transition | let q=t.src.pstate,q"=t.dest.pstate,s=t.src.bstate,s"=t.dest.bstate {
		q->t.label.plabel->q" in T_Q
		s->q.label->s" in T_S	
		t.label.blabel = q.label
	}
}

pred all_product_transitions_exist {
	all q,q": Q, t,t": S, op: Operation, e: Sigma |
		(e = q.label and q->op->q" in T_Q and t->e->t" in T_S) => some s,s": State, tr: Transition |
			q=s.pstate and q"=s".pstate and t=s.bstate and t"=s".bstate and tr.src = s and tr.dest = s" and tr.label.plabel = op and tr.label.blabel = e
}

fun prod_action[op: Operation, e: Sigma] : one Action {
	{ a: Action | a.plabel=op and a.blabel=e }
}

pred independent[op,op": Operation] {
	all q: Q | (op in q.enabled_Q and op" in q.enabled_Q) => {
		op in op".(q.T_Q).enabled_Q
		op" in op.(q.T_Q).enabled_Q
		op.((op".(q.T_Q)).T_Q) =	op".((op.(q.T_Q)).T_Q)
	}
}

pred invisible[op: Operation] {
	all q: (enabled_Q.op) | q.label = op.(q.T_Q).label
}
--------- ample sets
fun amp[q: Q, s: S] : set Action {
	{ a: Action | a.plabel in ample[q][s] }
}

pred C0 {
	all s: State | some s.pstate.enabled_Q => some s.r
}
pred C1 {
	all s: State |
		let _r = { q1,q2: Q | some a: Action-s.r | q1->a.plabel->q2 in T_Q } |
			all q": s.pstate.*_r, op: q".(enabled_Q)-(s.r.plabel), op": s.r.plabel | independent[op,op"]
}
pred C2 {
	all s: State | s.r.plabel != s.pstate.enabled_Q => all a: s.r | invisible[a.plabel]
}

pred C3"_1 {
	let _r = {s,s": State | s->s" in succ_r and s.r.plabel != s.pstate.enabled_Q } |
		no s: State | s in s.^_r
}

--------- por correctness
pred accepting[_r: State->State] {
	some s: Init.*_r | (s.bstate in Accepting and s in s.^_r)
}

pred correctness {
	accepting[succ] => accepting[succ_r]
}
