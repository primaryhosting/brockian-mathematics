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

lemma sgn_flipAt_of_lt {x : Fin n → Bool} {i j : Fin n} (h : j < i) :
    sgn (flipAt x i) j = sgn x j := by
  have hfilter : Finset.univ.filter (fun k => k < j ∧ flipAt x i k = true)
      = Finset.univ.filter (fun k => k < j ∧ x k = true) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt (hk.trans h))] at hx⟩
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt (hk.trans h))]⟩
  unfold sgn
  rw [hfilter]

/-- Flipping a coordinate `i` reverses the sign at a larger index `j`. -/
