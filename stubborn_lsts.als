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
	(p in lassos and q in lassos) => {
		#p.tr > #q.tr implies reduces_to[p,q]
		#q.tr > #p.tr implies reduces_to[q,p]
		// otherwise, they have the same stutter-free pairs
		#p.tr = # q.tr implies (p.w_pre = q.w_pre and p.w_inf = q.w_inf)
	} else p.w_pre = q.w_pre
}

// return the number of indices in p that are smaller than i
fun _f[i: Int, p: set Int] : Int {
	#{ j: p | j < i }
}

// return the sequence of state labels along a path (trace)
fun _trace[tr: seq Transition] : seq AP {
	tr.src.label.add[tr.last.dest.label]
}

// remove stuttering from a trace
fun _no_stut[trace: seq AP] : seq AP {
	let ids = { i: trace.inds | i = 0 or trace[i] != trace[minus[i,1]] } |
		{ i: Int, l: AP | some j: ids | l = trace[j] and i = _f[j, ids] }
}

// return the no-stutter trace of a lasso, up to the start of cycle
// and the no-stutter trace of the entire path if deadlocking
fun w_pre[p: Path] : seq AP {
	p in P_e => { 0-> p.start.label } else {
		p in lassos => {
			let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end },
			pre =  p.tr.subseq[0,minus[start,1]],
			trace = pre._trace._no_stut |
				// corner case: when the stutter happens right at the start of the cycle
				trace.last = p.tr[start].src.label => trace.butlast else trace
		} else p.tr._trace._no_stut
	}
}

// return the no-stutter trace of the cycle of a lasso
// and the empty sequence if deadlocking
fun w_inf[p: Path] : seq AP {
	p not in lassos => p.tr.subseq[-1,-1] else {
		let start = { i: Int | some p.tr[i] and p.tr[i].src = p.end },
		cycle = p.tr.subseq[start,#p.tr.inds],
		trace = cycle._trace._no_stut |
			// corner case: when the stutter happens right before the end of the cycle
			// corner corner case: when the entire cycle stutters on the same label
			trace.last = trace.first and #trace.inds > 1 => trace.butlast else trace
	}
}

fun _pref[p: seq AP, i: Int] : seq AP {
	p.subseq[0, minus[i,1]]
}

fun _suff[p: seq AP, i: Int] : seq AP {
	p.subseq[i, p.inds.max]
}

pred reduces_to[p,q: Path] {
	let w_pre_p = p.w_pre, w_inf_p = p.w_inf, w_pre_q = q.w_pre, w_inf_q = q.w_inf {
	{ // case (s t*k, t) -> (s, t)
		w_inf_p = w_inf_q
		some k: Int {
			let tau = w_inf_p, i = w_pre_p.idxOf[tau.first], sigma = _pref[w_pre_p, i] {
				k >= 0
				_suff[w_pre_p, i] = _repeat[tau, k]
				w_pre_q = sigma
			}
		}
	} or 
	{ // case (s p, t p) -> (s, p t)
		some i: w_inf_p.inds, j: w_pre_p.inds {
			let tau = _pref[w_inf_p, i], rho = _suff[w_inf_p, i], sigma = _pref[w_pre_p, j] {
				w_inf_q = append[rho, tau]
				w_pre_q = sigma
				rho = _suff[w_pre_p, j]
			}
		}
	}
}}

// return a sequence consisting of p repeated k times
// note: the length of the new sequence should fit inside the seq bound
fun _repeat[p: seq AP, k: Int] : seq AP {
	k > 2 => p.append[p].append[p] else (k > 1 => p.append[p] else (k > 0 => p else p.subseq[-1,-1])) // the last case is a trick to return the empty sequence
}
