/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The hypercube and its signed adjacency operator -/

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a point of the Boolean hypercube. -/

lemma sgn_flipAt_self (x : Fin n → Bool) (i : Fin n) : sgn (flipAt x i) i = sgn x i := by
  have hfilter : Finset.univ.filter (fun k => k < i ∧ flipAt x i k = true)
      = Finset.univ.filter (fun k => k < i ∧ x k = true) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt hk)] at hx⟩
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt hk)]⟩
  unfold sgn
  rw [hfilter]


/-! ## Huang's signed adjacency operator -/

/-- Huang's signed adjacency operator of the `n`-dimensional hypercube, acting on
real-valued functions on `Fin n → Bool`. -/
