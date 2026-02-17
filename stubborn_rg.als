module stubborn_rg

open lib/lsts[Label,Action] as lsts
open util/ordering[Strategy] as ord_strategy

sig Label {}
one sig P1, P2, goal extends Label {}
one sig bot {}
sig Action {}
sig A1, A2 in Action {}

sig State extends AState {
	interesting: set Action
}{
	some enabled & A1 <=> P1 in label
	some enabled & A2 <=> P2 in label

	goal not in label => (all g: Goal, p: path[this,g] | some p.actions & interesting)
}
one sig Init extends State {}

sig Strategy {
	move: State -> one {A1 + bot} 
}

fact {
	rooted_at [Init]
	valid_strategies
	all_strategies_exist
	Action = A1+A2
	no A1 & A2
	deterministic
}

fun at [s: Strategy, i: State]: lone { A1 + bot } { i.(s.move) }
fun inds [s: Strategy] : set State { A1.~(s.move) + bot.~(s.move) }
fun at [s: State -> one {A1+ bot}, i: State]: lone { A1 + bot } { i.s }

pred valid_strategies {
	all st: Strategy {
		all s: State | some enabled[s] & A1 => (st.at[s] in enabled[s] & A1) else st.at[s] = bot
	}	
}

// a strategy sigma(s) that is valid in the full game may not be valid in the reduced game
// i.e. if the action sigma(s) is not present in the reduced game
pred valid_r_strategy[st: State -> one {A1 + bot}, s: State] {
	some enabled[s] & A1 & s.r => (f[st,s] in enabled[s] & A1 & s.r) else f[st,s] = bot
}

// reduce strategy
fun f[st: State -> one {A1+ bot}, s: State] : A1 + bot {
	{ a: A1 + bot | st.at[s] in s.r => a = st.at[s] else a = bot }
}

pred all_strategies_exist {
	all s: State, a: enabled[s] & A1 | some st: Strategy | s->a in st.move

	all disj st, st": Strategy {
		let diffs1 = st".move - st.move |
			all i: diffs1.{ Action + bot } | some st"": Strategy |
				st"".move = {st".move - { i -> st".at[i] }} + { i -> st.at[i] }
		let diffs2 = st.move - st".move |
			all i: diffs2.{ Action + bot } | some st"": Strategy |
				st"".move = {st.move - { i -> st.at[i] }} + { i -> st".at[i] }
	}
}

fun Goal : State {
	{ s: State | goal in s.label }
}

fun path[s,s":State] : Path {
	{p: Path | start[p]=s and end[p]=s"}
}

fun safe[s: State] : Action {
	{ a: enabled[s] & A1 | all disj q,p: Path | (no enabled[s] & A2 and start[p]=s and actions[p] in A1-a and no enabled[p.end] & A2 and start[q]=s and q.tr.label.first=a and q.tr.label.rest=p.tr.label) => no enabled[q.end] & A2 }
}

fun next_s[s: State, st: State -> one {A1 + bot}] : Action {
	st.at[s] != bot => (enabled[s] & A2 + st.at[s]) else enabled[s] & A2
}

fun next_s_r[s: State, st: State -> one {A1 + bot}] : Action {
	f[st,s] != bot => (enabled[s] & A2 + f[st,s]) else enabled[s] & A2
}

pred consistent [p: Path, st: State -> one {A1 + bot}] {
	all t: p.tr.elems | some a: next_s[t.src,  st] | t.label = a
}

pred r_consistent [p: Path, st: State -> one {A1 + bot}] {
	all t: p.tr.elems | some a: next_s_r[t.src,  st] & t.src.r | t.label = a
}

// player p1 wins state s
pred win_state [s: State] {
	some st: Strategy {
		all p: start.s & P_c | consistent[p,st.move] implies (some t: stateset[p] | t in Goal)	
	}
}
// player p1 wins state s in the reduced game
pred r_win_state [s: State] {
	some st: Strategy {
		all t: State | valid_r_strategy[st.move, t]
		all p: start.s & P_c_r | r_consistent[p,st.move] implies (some t: stateset[p] | t in Goal)
	}
}

pred I {
	all s: State |
	(some enabled[s] & A1 and some enabled[s] & A2) => enabled[s] in s.r
}

pred W {
	all s: State, a: s.r |
	let P = { p: start.s-P_e | (no p.tr.label.elems & s.r) and a in enabled[p.end] } |
	all p: P | some t": seq Transition |
		(valid_trseq[t"] and t".first.label=a and t".first.src=s and t".last.dest=a.(p.end.T) and t".rest.label=p.tr.label)
}

pred R {
	all s: State | s.interesting in s.r
}

pred G1 {
	all p: Path | let s = start[p], s" = end[p] |
	actions[p] in Action-s.r and no enabled[s] & A2 => no enabled[s"] & A2
}

pred G2 {
	all p: Path | let s = start[p], s" = end[p] |
	actions[p] in Action-s.r and no enabled[s] & A1 => no enabled[s"] & A1
}

pred S {
	all s: State |
	enabled[s] & A1 & s.r in safe[s] or enabled[s] & A1 in s.r
}

pred C {
	all a: A2, p: Path |
	(actions[p] in A2 and cycle[p]) => a in p.start.r
}

pred D {
	all s: State |
	some enabled[s] & A2 => some a: enabled[s] & A2 & s.r | all p: Path | p.start=s and actions[p] in Action-s.r => a in enabled[p.end] & A2
}

pred V {
	all s: State, p: start.s |
	(actions[p] in A2 and p.end in Goal) => enabled[s] & A2 in s.r
}

pred correctness {
	all s: State | win_state[s] iff r_win_state[s]
}
