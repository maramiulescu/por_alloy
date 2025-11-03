module stubborn_pg
open lib/blsts[Int, Action] as blsts

sig Action {}
one sig Even {} // diamond
one sig Odd {}

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

fact {
	rooted_at [Init]
	valid_strategies
	all_strategies_exist
}

fun at [s: Strategy, i: State]: lone State { i.(s.move) }
fun at [s: S_e -> one State, i: State]: lone State { i.s }

pred valid_strategies {
	all st: Strategy | st.move in succ 
	all disj s1,s2: Strategy | s1.move != s2.move
}

// a strategy sigma(s) that is valid in the full game may not be valid in the reduced game
// i.e. if the state sigma(s) is not reachable in the reduced game
pred valid_r_strategy[st: State -> one State, s: State] {
	s->st.at[s] in succ_r
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

fun min_priority[p: Path] : one Int {
	let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end } |
	let cycle = p.tr.subseq[start,#p.tr.inds].src.elems + p.end |
		integer/min[cycle.label]
}

pred odd_priority[i: Int] { rem[i,2] = 1 }

pred keyAction[a: Action, s: State] {
	let reach = { t,t": State | some b: Action-s.r | t->b->t" in T } |
		all s": s.*reach | a in s".enabled
}


pred consistent [p: Path, st: S_e -> one State] {
	all t: p.tr.elems | t.src.player = Even iff st.at[t.src] = t.dest
}

// player Even wins state s
pred win_state [s: State] {
	some st: Strategy {
		all p: start.s & P_c| consistent[p, st.move] implies win_path[p]
	}
}

// player Even wins state s in the reduced game
pred r_win_state [s: State] {
	some st: Strategy {
		all t: State | valid_r_strategy[st.move, t]
		all p: start.s & P_c_r | consistent[p, st.move] implies win_path[p]
	}
}

// player Even wins path pi
pred win_path [pi: Path] {
	some pi
	is_lasso[pi] => !odd_priority[pi.min_priority] else pi.end.player = Odd
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