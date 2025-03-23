open ample_pa as pa

one sig S1 extends S {}
one sig p,empty extends Sigma {}

pred test {
	C0 and C1 and C2 and C3"_1

	// Buchi automaton
	S <: T = Sinit->empty->Sinit + Sinit->empty->S1 + S1->p->S1
	Accepting = S1
}

check { test => correctness } for 4 State, 5 Transition, 2 Q, 2 S, 2 Operation, 2 Sigma, 4 Action, 1 Path