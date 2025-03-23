module stubborn_lsts
open lib/blsts[AP, Action] as blsts

sig AP {}
sig Action {}
sig State extends AState {}{
	one label
}
one sig Init extends State {}

fact {
	rooted_at [Init]
}

let Viz = { a: Action | some t: Transition | t.label = a and t.src.label != t.dest.label }
let Inv = Action - Viz

pred keyAction[a: Action, s: State] {
	let reach = { t,t": State | some b: Action-s.r | t->b->t" in T } |
		all s": s.*reach | a in s".enabled
}

pred D1 {
	all s: State, a: s.r |
		let P = { p: start.s-P_e | (no p.tr.label.elems & s.r) and a in p.end.enabled } |
		all p: P | some t": seq Transition |
			(valid_trseq[t"] and t".first.label=a and t".first.src=s and t".last.dest=a.(p.end.T) and t".rest.label=p.tr.label)
}

pred D1" {
	all s: State, a: s.r |
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
	all a: Viz, p: cycles | some s: p.stateset| a in s.r
}

pred correctness {
	all p: start.Init & P_c |
		some q: start.Init & P_c & P_r |
			stutter_equiv[p.tr,q.tr]
}

pred correctness_tr {
	all p: start.Init & P_c |
		some t: seq Transition {
			t.first.src=Init
			valid_trseq[t]
			complete_trseq[t]
			reduced_trseq[t]
			stutter_equiv[p.tr, t]
	}
}

pred stutter_equiv[p,q: seq Transition] {
	let no_stut_p = { i: Int | let t=p[i] | some t and t.src.label != t.dest.label } |
	let no_stut_q = { i: Int | let t=q[i] | some t and t.src.label != t.dest.label } |
	#no_stut_p = #no_stut_q and all i: no_stut_p, j: no_stut_q |
		f[i,no_stut_p] = f[j,no_stut_q] => (p[i].src.label=q[j].src.label and p[i].dest.label=q[j].dest.label)
}

fun f[i: Int, p: set Int] : Int {
	#{ j: p | j > i }
}