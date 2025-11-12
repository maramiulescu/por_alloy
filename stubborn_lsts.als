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
		some q: start.Init & P_c_r |
			stutter_eq[p,q]
}

pred stutter_eq[p,q: Path] {
	(no p.end.enabled and no q.end.enabled and stutter_eq_deadlock[p,q]) or (is_lasso[p] and is_lasso[q] and stutter_eq_lasso[p,q])
}

pred stutter_eq_deadlock[p,q: Path] {
	p.tr.alternations = q.tr.alternations
}

pred stutter_eq_lasso[p,q: Path] {
	#p.tr.alternations > #q.tr.alternations implies p.tr.butlast.alternations = q.tr.alternations
	#q.tr.alternations > #p.tr.alternations implies q.tr.butlast.alternations = p.tr.alternations
	Int.(p._cycle.alternations) = Int.(q._cycle.alternations)
}

fun _cycle[p: Path] : seq Transition {
	// start of cycle in path
	let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end } |
		p.tr.subseq[start,#p.tr.inds]
}

fun alternations[tr: seq Transition] : seq State->State {
	let no_stut = { i: tr.inds, t: Transition | i->t in tr and t.src.label != t.dest.label } |
	{ i: Int, l,l": AP | some t: no_stut.elems | l = t.src.label and l" = t.dest.label and i = _f[idxOf[no_stut, t], no_stut.inds] }
}

fun _f[i: Int, p: set Int] : Int {
	#{ j: p | j < i }
}
