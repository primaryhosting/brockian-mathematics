import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Unitary

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace of a matrix. -/

lemma frobSq_posProj : frobSq (posProj hA) = (posIndex hA : ℝ) := by
  rw [posProj, frobSq_specM, posIndex, Fintype.card_subtype]
  simp

end Projections

/-! ## The rank-trace inequality -/

/-- **Rank-trace inequality** (Lemma 3.2).  Let `P` and `Q` be Hermitian complex matrices of
size `d`, with `P` positive semidefinite of rank at most `r`, and with `Q` having at most `b`
strictly positive eigenvalues.  Then for every `c > 0`,
`c * rtrace P - (c²/4) * r + 2 * c * rtrace Q - c² * b ≤ frobSq (P + Q)`. -/
