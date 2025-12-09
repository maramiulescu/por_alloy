module ample_synth_mpa
open lib/blsts[Label,Action] as blsts
//open util/ordering[Strategy] as ord_str

sig Label {}
one sig P1, P2, goal extends Label {}
one sig bot {}
sig Action {}
sig a1, a2 in Action {}

sig State extends AState {

}{
	some enabled & a1 <=> P1 in label
	some enabled & a2 <=> P2 in label
}
one sig Init extends State {}

sig Strategy {
	move: State -> one {a1 + bot} 
}

fact {
	rooted_at [Init]
	valid_strategies
	all_strategies_exist
	Action = a1+a2
	no a1 & a2
	deterministic
}

fun at [s: Strategy, i: State]: lone { a1 + bot } { i.(s.move) }
fun inds [s: Strategy] : set State { a1.~(s.move) + bot.~(s.move) }
fun at [s: State -> one {a1+ bot}, i: State]: lone { a1 + bot } { i.s }

pred valid_strategies {
	all st: Strategy {
		all s: State | some s.enabled & a1 => (st.at[s] in s.enabled & a1) else st.at[s] = bot
	}	
}

// a strategy sigma(s) that is valid in the full game may not be valid in the reduced game
// i.e. if the action sigma(s) is not present in the reduced game
pred valid_r_strategy[st: State -> one {a1 + bot}, s: State] {
	some s.enabled & a1 & r[s] => (f[st,s] in s.enabled & a1 & r[s]) else f[st,s] = bot
}

// reduce strategy
fun f[st: State -> one {a1+ bot}, s: State] : a1 + bot {
	{ a: a1 + bot | st.at[s] in r[s] => a = st.at[s] else a = bot }
}

pred all_strategies_exist {
	all s: State, a: s.enabled & a1 | some st: Strategy | s->a in st.move

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

fun next_s[s: State, st: State -> one {a1 + bot}] : Action {
	st.at[s] != bot => (s.enabled & a2 + st.at[s]) else s.enabled & a2
}

fun next_s_r[s: State, st: State -> one {a1 + bot}] : Action {
	f[st,s] != bot => (s.enabled & a2 + f[st,s]) else s.enabled & a2
}

pred consistent [p: Path, st: State -> one {a1 + bot}] {
	all t: p.tr.elems | some a: next_s[t.src,  st] | t.label = a
}

pred r_consistent [p: Path, st: State -> one {a1 + bot}] {
	all t: p.tr.elems | some a: next_s_r[t.src,  st] & r[t.src] | t.label = a
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

pred independent [s: State, a: a1, b: a1] {
	a in s.enabled
	b in s.enabled
	no (s.enabled & a2)
	let s1 = T[s,a], s2 = T[s,b] |
	no (s1.enabled & a2) and no (s2.enabled & a2) and b in s1.enabled and a in s2.enabled and T[s1,b] = T[s2,a] and no T[s1,b].enabled & a2
}

pred A1 {
	all s: State | (some s.enabled) implies (some s.r)
}

pred A2 {
	all p: Path | let s = start[p] |
	all a: s.r | not independent[s, a, p.tr.last.label] implies (some t: Transition | t in p.tr.elems and t.label in s.r)
}

pred A3 {
	all s: State | (s.enabled & a2) in s.r
}

// A4 is modelled by a Goal state labelling

pred A51 {
	all s: State, a: s.r | some T[s,a].enabled & a2 implies s.r = s.enabled
}

pred A52 {
	all s: State, a: s.enabled, b: s.enabled | all s1: T[s,b] | some T[s1,a].enabled & a2 implies (a in s.r iff b in s.r)
}

pred correctness {
	all s: State | win_state[s] iff r_win_state[s]
}
