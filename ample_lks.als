module ample_lks
open lib/blsts[AP, Action] as blsts

sig AP {}
sig AP" in AP {} // interesting atomic propositions
sig Action {}
sig Action" in Action {} // interesting actions
sig State extends AState {}
one sig Init extends State {}

fact {
	rooted_at [Init]
}

pred invisible [a: Action] {
	a not in Action"
	all t: Transition |
		t.label = a => t.src.label & AP" = t.dest.label & AP"
}

// paths p and p" have the same sequence of visible actions
pred weakly_eq [p,p": Path] {
	let a = { i: Int | some p.tr[i] and not p.tr[i].label.invisible }, a" = { i: Int | some p".tr[i] and not p".tr[i].label.invisible } |
		#a=#a" and all i: a, j: a" | f[i,a] = f[j,a"] => p.tr[i].label = p".tr[j].label
}

fun f[i: Int, p: set Int] : Int {
	#{ j: p | j > i }
}

pred state_event_eq [p,p": Path] {
	let sig_p = { i: Int | let t=p.tr[i] | some t and t.label in Action" and t.src.label&AP"!=t.dest.label&AP" } |
	let sig_p" = { i: Int | let t=p".tr[i] | some t and t.label in Action" and t.src.label&AP"!=t.dest.label&AP" } |
	#sig_p = #sig_p" and all i: sig_p, j: sig_p" |
		f[i,sig_p] = f[j,sig_p"] => (p.tr[i].src.label&AP"=p".tr[j].src.label&AP" and p.tr[i].dest.label&AP"=p".tr[j].dest.label&AP")
}

pred correctness {
	all p,p": start.Init & P_c |
		weakly_eq[p,p"] => state_event_eq[p,p"]
}
