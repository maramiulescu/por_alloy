module lib/blsts [Label, A]

// symmetry breaking
open util/ordering[A] as ord_a
open util/ordering[AState] as ord_state
open util/ordering[Path] as ord_path
open util/ordering[Label] as ord_label --disable for PG
open util/ordering[Transition] as ord_tr

abstract sig AState {
	label: set Label,
	r: set A // reduction function r
}

sig Transition {
	src: one AState,
	label: one A,
	dest: one AState
}

sig Path {
	start: one AState,
	end: one AState,
	tr: seq Transition
}

let P_e = { p: Path | no p.tr } // empty paths
let P_r = { p: Path | all t: p.tr.elems | t.label in r[t.src] } // reduced paths
let P_c = { p: Path | no p.end.enabled or is_lasso[p] } // complete paths
let P_c_r = { p: Path | (no p.end.enabled & p.end.r or is_lasso[p]) and all t: p.tr.elems | t.label in r[t.src] } // complete reduced paths
let lassos = { p: Path | is_lasso[p] }

// transition relation
fun T: AState -> A -> AState {
	{ s: AState, a: A, s": AState | some t: Transition | t.src = s and t.label = a and t.dest = s" }
}

fun succ: AState -> set AState {
	{ s, s": AState | s" in src.s.dest }
}

fun succ_r: AState -> set AState {
	{ s, s": AState | some a: s.r | s->a->s" in T }
}

// actions enabled in s
fun enabled[s: AState] : set A {
	s.T.AState
}

fun stateset[p: Path] : set AState {
	p.start + p.tr.dest.elems
}

fun actions[p: Path] : set A {
	p.tr.label.elems
}

pred valid_transitions {
	all disj t,t": Transition | !(t.src=t".src and t.dest=t".dest and t.label=t".label)
}

pred valid_paths {
	all disj p,p": Path | !(p.start=p".start and p.end=p".end and p.tr=p".tr)
	all p: P_e | p.start = p.end
	all p: Path - P_e {
		p.start = p.tr.first.src
		p.end = p.tr.last.dest
	}
	all p: Path | valid_path[p]
}

pred valid_path[p: Path] {
	-- follows the transition relation
	valid_trseq[p.tr]
	-- is finite with no state repetitions or lasso	
	add[#(p.tr.inds),1] = #(p.stateset) or is_lasso[p]
}

pred is_lasso[p: Path] {
	#(p.tr.inds) = #(p.stateset) and p.end in p.tr.src.elems
}

pred valid_trseq[tr: seq Transition] {
	all i: tr.inds | let t1 = tr[i], t2 = tr[add[i,1]] |
		(some t1 and some t2) => t1.dest = t2.src
}

pred complete_trseq[tr: seq Transition] {
	no tr.last.dest.enabled or (let stateset = tr.first.src + tr.dest.elems {
		#tr.inds >= #stateset and tr.last.dest in tr.src.elems
	})
}

pred reduced_trseq[tr: seq Transition] {
	all t: tr.elems | t.label in r[t.src]
}

--- make sure there is some reduction in the initial state
pred redundancy [init: one AState] { some init.r and some init.enabled - init.r and some init.enabled & init.r }

pred cycle[p: Path] {
	p.start in p.end.succ
}

pred all_paths_exist {
	all s: AState | one p: Path | p.start = s and p.end = s and no p.tr
	all p: Path, t: Transition |
		valid_path[p,t] => some q: Path | q.tr=p.tr.add[t]
}

pred all_init_paths_exist [init: one AState] {
	one p: Path | p.start = init and p.end = init and no p.tr
	all p: Path, t: Transition |
		valid_path[p,t] => some q: Path | q.tr=p.tr.add[t]
}

// path p remains valid after appending transition t
pred valid_path [p: Path, t: Transition] {
	let tr" = p.tr.add[t] {
		t.src = p.end
		-- follows the transition relation
		all i: tr".inds | let t1 = tr"[i], t2 = tr"[add[i,1]] |
			(some t1 and some t2) => t1.dest = t2.src
		-- is finite with no state repetition or a lasso	
		add[#(tr".inds),1] = #(p.stateset + t.dest) or (add[#(p.tr.inds),1] = #p.stateset and t.dest in p.stateset)
	}
}

// all states are reachable from s
pred rooted_at[s: AState] {
	s.*succ = AState
}

fact {
	valid_paths
	valid_transitions
}
