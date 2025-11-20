module stubborn_lsts
open lib/blsts[AP, Action] as blsts

sig AP {}
sig Action {}
sig State extends AState {}{
	one label
}
one sig Init extends State {}
one sig epsilon {}

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
	let trace = p._pre._trace._no_stut |
	// corner case: when the stutter happens right at the start of the cycle
		trace.last = p._cycle._trace.first => trace.butlast else trace
}

// return the no-stutter trace of the cycle of a lasso
fun _w_inf[p: Path] : seq AP {
	let trace = p._cycle._trace._no_stut |
	// corner case: when the stutter happens right before the end of the cycle
	// corner corner case: when the entire cycle stutters on the same label
		trace.last = trace.first and #trace.inds > 1 => trace.butlast else trace
}

// t is a subsequence of s
pred is_subseq[s, t: seq AP] {
	let R = { i: s.inds, j: t.inds | s[i] = t[j] } {
		all i: t.inds | some i.R // all indices of t appear in s
		all i,j: t.inds | i < j implies i.R < j.R // all indices of t appear in the same order in s
		 // all indices of t appear consecutively in s
	}
}

fun _pre[p: seq AP, i: Int] : seq AP {
	p.subseq[0, minus[i,1]]
}

fun _suf[p: seq AP, i: Int] : seq AP {
	p.subseq[i, p.inds.max]
}

pred reduces_to[w_pre_p, w_inf_p, w_pre_q, w_inf_q: seq AP] {
	some i: w_inf_p.inds, j: w_pre_p.inds {
		let tau = _pre[w_inf_p, i], rho = _suf[w_inf_p, i], sigma = _pre[w_pre_p, j] {
			w_inf_q = append[rho, tau]
			w_pre_q = sigma
			rho = _suf[w_pre_p, j]
		}
	}
}

pred stutter_eq_lasso[p,q: Path] {
	#p.tr > #q.tr implies reduces_to[p._w_pre, p._w_inf, q._w_pre, q._w_inf]
	#q.tr > #p.tr implies reduces_to[q._w_pre, q._w_inf, p._w_pre, p._w_inf]
	// otherwise, they have the same stutter-free pairs
	#p.tr = # q.tr implies (p._w_pre = q._w_pre and p._w_inf = q._w_inf)
}
