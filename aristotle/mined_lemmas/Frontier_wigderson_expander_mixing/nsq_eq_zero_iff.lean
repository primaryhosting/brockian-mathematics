/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

section Mixing

variable {n : ℕ}

/-- The bilinear form `xᵀ A y` associated with a real matrix `A`. -/

lemma nsq_eq_zero_iff (x : Fin n → ℝ) : nsq x = 0 ↔ ∀ i, x i = 0 := by
  unfold nsq
  constructor
  · intro h i
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j))).1 h i (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  · intro h
    exact Finset.sum_eq_zero fun i _ => by rw [h i]; ring

/-- Polarization: the bilinear form is controlled by the quadratic form. -/
