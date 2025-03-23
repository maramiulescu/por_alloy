module stubborn_rg
open lib/blsts[Label,Action] as blsts

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
	move: State -> lone {A1 + bot} 
}

fact {
	rooted_at [Init]
	valid_strategies
	all_strategies_exist
	Action = A1+A2
	no A1 & A2
}

fun at [s: Strategy, i: State]: lone { A1 + bot } { i.(s.move) }
fun inds [s: Strategy] : set State { A1.~(s.move) + bot.~(s.move) }

pred valid_strategies {
		all st: Strategy {
			all s: State | some s.enabled & A1 => st.at[s] in s.enabled & A1 else st.at[s] = bot
		}
}
pred all_strategies_exist {
	all s: State, a: s.enabled & A1 | some st: Strategy | s->a in st.move

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
	{ a: s.enabled & A1 | all disj q,p: Path | (no s.enabled & A2 and start[p]=s and actions[p] in A1-a and no end[p].enabled & A2 and start[q]=s and q.tr.label.first=a and q.tr.label.rest=p.tr.label) => no end[q].enabled & A2 }
}

fun next_s[s: State, st: Strategy] : Action {
	st.at[s] != bot => (s.enabled & A2 + st.at[s]) else s.enabled & A2
}

fun next_s_r[s: State, st: Strategy] : Action {
	st.at[s] != bot => ((s.enabled & A2 + st.at[s]) & r[s]) else (s.enabled & A2 & r[s])
}

fun consistent: Path -> Strategy {
	{ p: Path & P_c, st: Strategy | consistent[p,st] }
}
// play p is consistent with strategy st
pred consistent [p: Path, st: Strategy] {
	all t: p.tr.elems | some a: next_s[t.src, st] | t.label = a
}
// player p1 wins state s
pred win_state [s: State] {
	(some st: Strategy {
		some start.s & consistent.st
		all p: start.s & consistent.st | some t: stateset[p] | t in Goal
	}) or s in Goal and (no s.enabled or s in s.^succ)
}
// player p1 wins state s in the reduced game
pred r_win_state [s: State] {
	(some st: Strategy {
		some start.s & consistent.st & P_r
		all p: start.s & consistent.st & P_r | some t: stateset[p] | t in Goal
	}) or s in Goal and (no r[s] & s.enabled or s in s.^succ_r)
}

pred I {
	all s: State |
	(some s.enabled & A1 and some s.enabled & A2) => s.enabled in r[s]
}

pred W {
	all s: State, a: s.r |
	let P = { p: start.s-P_e | (no p.tr.label.elems & s.r) and a in p.end.enabled } |
	all p: P | some t": seq Transition |
		(valid_trseq[t"] and t".first.label=a and t".first.src=s and t".last.dest=a.(p.end.T) and t".rest.label=p.tr.label)
}

pred R {
	all s: State | s.interesting in r[s]
}

pred G1 {
	all p: Path | let s = start[p], s" = end[p] |
	actions[p] in Action-r[s] and no s.enabled & A2 => no s".enabled & A2
}

pred G2 {
	all p: Path | let s = start[p], s" = end[p] |
	actions[p] in Action-r[s] and no s.enabled & A1 => no s".enabled & A1
}

pred S {
	all s: State |
	s.enabled & A1 & r[s] in safe[s] or s.enabled & A1 in r[s]
}

pred C {
	all a: A2, p: Path |
	(actions[p] in A2 and cycle[p]) => a in r[start[p]]
}

pred D {
	all s: State |
	some s.enabled & A2 => some a: s.enabled & A2 & r[s] | all p: Path | start[p]=s and actions[p] in Action-r[s] => a in end[p].enabled & A2
}

pred V {
	all s: State, p: start.s |
	(actions[p] in A2 and end[p] in Goal) => s.enabled & A2 in r[s]
}

pred correctness {
	all s: State | win_state[s] iff r_win_state[s]
}
