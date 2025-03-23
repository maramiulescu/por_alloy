module stubborn_pg
open lib/blsts[Int, Action] as lsts

sig Action {}
one sig Even {} // diamond
one sig Odd {}

fact {
	rooted_at [Init]
	valid_strategies
	all_strategies_exist
}

sig State extends AState {
	player: one { Even + Odd }
}{
	label > 0 and label < 4
	one label
}
one sig Init extends State {}

let S_e = { s: State | s.player = Even }

let Viz = { a: Action | some t: Transition | t.label = a and (t.src.label != t.dest.label or t.src.player != t.dest.player) }
let Inv = Action - Viz

sig Strategy {
	move: S_e -> one State
}

fun min_priority[p: Path] : one Int {
	let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end } |
	let cycle = p.tr.subseq[start,#p.tr.inds].src.elems + p.end |
		integer/min[cycle.label]
}

pred keyAction[a: Action, s: State] {
	let reach = { t,t": State | some b: Action-s.r | t->b->t" in T } |
		all s": s.*reach | a in s".enabled
}

fun consistent: Path -> Strategy {
	{ p: Path & P_c, st: Strategy | consistent[p,st] }
}

pred odd_priority[i: Int] { rem[i,2] = 1 }

pred valid_strategies {
	all s: Strategy | s.move in succ 
	all disj s1,s2: Strategy | s1.move != s2.move
}

pred all_strategies_exist {
	all s: S_e, s": s.succ | some st: Strategy | s.(st.move) = s"

	all disj s1, s2: Strategy {
		let diff1 = s2.move - s1.move | all s: diff1.State | some s3: Strategy |
			s.(s3.move) = s.diff1 and all t: S_e-s | t.(s3.move) = t.(s2.move)
		let diff2 = s1.move - s2.move | all s: diff2.State | some s3: Strategy |
			s.(s3.move) = s.diff2 and all t: S_e-s | t.(s3.move) = t.(s2.move)
	}
}

// path pi is consistent with strategy s
pred consistent [p: Path, s: Strategy] {
	all t: p.tr.elems | t.src.player = Even <=> (t.src).(s.move) = t.dest
}

// player Even wins state s
pred win_state [s: State] {
	some st: Strategy {
		some start.s & consistent.st
		all p: start.s & consistent.st | win_path[p]
	}
}

// player Even wins state s in the reduced game
pred r_win_state [s: State] {
	some st: Strategy {
		some start.s & consistent.st & P_r
		all p: start.s & consistent.st & P_r | win_path[p]
	}
}

// player Even wins path pi
pred win_path [pi: Path] {
	some pi
	is_lasso[pi] => ! odd_priority[pi.min_priority] else pi.end.player = Odd
}

---- stubborn sets
pred D1" {
	all s:State, a: s.r |
		let P = { p: start.s-P_e | (no p.tr.label.elems & s.r) and a in p.end.enabled } |
		all p: P | some t": seq Transition |
			(valid_trseq[t"] and t".first.label=a and t".first.src=s and t".last.dest=a.(p.end.T) and t".rest.label=p.tr.label) and (a in Inv => all i: p.tr.inds | p.tr[i].dest->a->t"[add[i,1]].dest in T)
}

pred D2w {
	all s: State | some s.enabled => some a: s.r | keyAction[a,s]
}

pred V {
	all s: State | some s.enabled & s.r & Viz => Viz in s.r
}

pred I {
	all s: State | let key = { a: s.r | keyAction[a,s] } |
		some s.enabled & Inv => some Inv & key
}

pred L {
	let cycles = P_r & lassos |
		all a: Viz, p: cycles | some s: p.stateset | a in s.r
}

pred P {
	all s: State |
		(some a: s.r, t: State | s->a->t in T and s.player != t.player) => s.r = Action
}

pred correctness {
	all s: State | win_state[s] iff r_win_state[s]
}