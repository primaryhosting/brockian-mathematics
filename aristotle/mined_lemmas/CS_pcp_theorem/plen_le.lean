import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
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

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem plen_le (hq : 0 < V.qnum) : V.plen ≤ V.size := by
  have h1 : ∑ _i : Fin V.qnum, ∑ _j : Fin V.plen, 1 ≤ ∑ i, ∑ j, (V.query i j).size :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Circuit.one_le_size _
  have h2 : ∑ _i : Fin V.qnum, ∑ _j : Fin V.plen, 1 = V.qnum * V.plen := by
    simp [Finset.sum_const]
  have h3 : V.plen ≤ V.qnum * V.plen := Nat.le_mul_of_pos_left _ hq
  have h4 : (∑ i, ∑ j, (V.query i j).size) ≤ V.size := Nat.le_add_right _ _
  omega

