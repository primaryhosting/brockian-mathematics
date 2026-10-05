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

def hop (n : ℕ) : ((Fin n → Bool) → ℝ) →ₗ[ℝ] ((Fin n → Bool) → ℝ) where
  toFun v := fun x => ∑ i, sgn x i * v (flipAt x i)
  map_add' u v := by
    funext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext x
    simp [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

