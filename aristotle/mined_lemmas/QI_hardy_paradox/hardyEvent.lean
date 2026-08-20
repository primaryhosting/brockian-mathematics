/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Statement: Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file deliberately has no `import` lines so that the header above is the very first
-- thing in the file; the argument only uses `Bool`, `Fin` and `List` from Lean core.
-- A measure-theoretic (Mathlib) version of the same statement is in
-- `RequestProject/HardyMeasure.lean`.

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace QI

/-- Hardy's four events, in a local hidden-variable (local realistic) model.

A run `l : Λ` records the hidden state of the pair; `A i l` and `B j l` are the
predetermined outcomes (`true`/`false`) of Alice's measurement `i` and Bob's measurement `j`
on that run.  The outcome of each party depends only on that party's own setting: this is
exactly the locality assumption. -/

def hardyEvent {Λ : Type u} (A B : Fin 2 → Λ → Bool) (l : Λ) : Bool := A 0 l && B 0 l

/-- **Hardy's nonlocality argument.**

Consider a local hidden-variable model: a list `runs` of experimental runs, on each of which
the outcomes of *all four* measurements are predetermined by local functions
`A 0, A 1, B 0, B 1 : Λ → Bool`.  Hardy's four conditions are

* a nonzero fraction of the runs have `A 0 = true` and `B 0 = true`;
* no run has `A 0 = true` and `B 1 = false`;
* no run has `A 1 = false` and `B 0 = true`;
* no run has `A 1 = true` and `B 1 = true`.

These are contradictory — no inequality is needed.  Indeed, on any run of the first
(positive-fraction) kind, the second condition forces `B 1 = true`, the third then forces
`A 1 = true`, and the fourth is violated.  Since quantum mechanics predicts states and
measurements satisfying all four conditions (with the first event occurring with strictly
positive probability), local realism fails on a nonzero fraction of runs. -/
