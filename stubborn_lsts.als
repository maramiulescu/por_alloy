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

fun alternations[tr: seq Transition] : seq AP->AP {
	let no_stut = { i: tr.inds, t: Transition | i->t in tr and t.src.label != t.dest.label } |
	{ i: Int, l,l": AP | some t: no_stut.elems | l = t.src.label and l" = t.dest.label and i = _f[idxOf[no_stut, t], no_stut.inds] }
}

// return the number of indices in p that are smaller than i
fun _f[i: Int, p: set Int] : Int {
	#{ j: p | j < i }
}

// return the transitions that make up the cycle of a lasso
fun _cycle[p: Path] : seq Transition {
	let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end } |
		p.tr.subseq[start,#p.tr.inds]
}

// return the transitions that precede the cycle of a lasso
fun _pre[p: Path] : seq Transition {
	let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end } |
		p.tr.subseq[0,minus[start,1]]
}

// return the sequence of state labels along a path (trace)
fun _trace[tr: seq Transition] : seq AP {
	tr.src.label
}

// remove stuttering from a trace
fun _no_stut[trace: seq AP] : seq AP {
	let ids = { i: trace.inds | i = 0 or trace[i] != trace[minus[i,1]] } |
		{ i: Int, l: AP | some j: ids | l = trace[j] and i = _f[j, ids] }
}

// return the no-stutter trace of a lasso, up to the start of cycle
fun _w_pre[p: Path] : seq AP {
	// corner case: when the stutter happens right at the start of the cycle
	let trace = (p._pre._trace.last = p._cycle._trace.first) => p._pre._trace.butlast else p._pre._trace |
		trace._no_stut
}

// return the no-stutter trace of the cycle of a lasso
fun _w_inf[p: Path] : seq AP {
	p._cycle._trace._no_stut
}

// longest rho
fun _rho[w_pre: seq AP, w_inf: seq AP] : seq AP {
	{ i: Int, l: AP | l = w_inf[i] and some j: Int | l = w_pre[j] }
}

// t is a subsequence of s
pred is_subseq[s: seq AP, t: seq AP] {
	let R = { i: s.inds, j: t.inds | s[i] = t[j] } {
		all i: t.inds | some i.R // all indices of t appear in s
		all i,j: t.inds | i < j implies i.R < j.R // all indices of t appear in the same order in s
		 // all indices of t appear consecutively in s
	}
}

// todo: fix out-of-order indices after append.
fun _tau[w_pre: seq AP, w_inf: seq AP] : seq AP {
	let rho = _rho[w_pre, w_inf] |
		{ i: Int, l: AP | {0 -> l}.append[rho] = w_inf.subseq[i, #rho] and some j: Int | {0 -> l}.append[rho] = w_pre.subseq[j, #rho] }
}
