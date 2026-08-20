import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Matrix

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form attached to a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

theorem posIndex_of_posDef {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.PosDef) : posIndex Q = Fintype.card m := by
  rw [posIndex, dif_pos hQ.1]
  have h : ∀ i, 0 < hQ.1.eigenvalues i := fun i => hQ.eigenvalues_pos i
  simp [h, Nat.card_eq_fintype_card]

end Sanity

end Zeta23Core

