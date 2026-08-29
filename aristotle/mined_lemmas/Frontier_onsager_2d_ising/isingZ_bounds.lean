/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/

lemma isingZ_bounds (L : ℕ) (K : ℝ) :
    2 ^ (L * L) * Real.exp (-(2 * |K| * (L * L : ℕ))) ≤ isingZ L K ∧
      isingZ L K ≤ 2 ^ (L * L) * Real.exp (2 * |K| * (L * L : ℕ)) := by
  have key : ∀ σ : Config L, |(-K) * energy L σ| ≤ 2 * |K| * (L * L : ℕ) := by
    intro σ
    rw [abs_mul, abs_neg]
    calc |K| * |energy L σ| ≤ |K| * (2 * (L * L : ℕ)) := by
          exact mul_le_mul_of_nonneg_left (abs_energy_le L σ) (abs_nonneg K)
      _ = 2 * |K| * (L * L : ℕ) := by ring
  constructor
  · rw [← sum_const_config L (Real.exp (-(2 * |K| * (L * L : ℕ))))]
    refine Finset.sum_le_sum (fun σ _ => Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (key σ)).1
    linarith
  · rw [← sum_const_config L (Real.exp (2 * |K| * (L * L : ℕ)))]
    refine Finset.sum_le_sum (fun σ _ => Real.exp_le_exp.2 ?_)
    exact (abs_le.1 (key σ)).2

/-- The Onsager integrand degenerates at `K = 0`, where the formula gives `log 2`. -/
