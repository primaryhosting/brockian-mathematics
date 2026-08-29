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

theorem query_size_le (i : Fin V.qnum) (j : Fin V.plen) : (V.query i j).size ≤ V.size := by
  have h1 : (V.query i j).size ≤ ∑ j', (V.query i j').size :=
    Finset.single_le_sum (f := fun j' => (V.query i j').size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j', (V.query i j').size) ≤ ∑ i', ∑ j', (V.query i' j').size :=
    Finset.single_le_sum (f := fun i' => ∑ j', (V.query i' j').size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (h1.trans h2).trans (Nat.le_add_right _ _)

