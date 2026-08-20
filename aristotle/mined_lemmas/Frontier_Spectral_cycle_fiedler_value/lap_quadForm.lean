/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma lap_quadForm (x : ZMod (m + 3) → ℝ) :
    x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
      = ∑ i : ZMod (m + 3), (x i - x (i + 1)) ^ 2 := by
  have h1 : x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
      = ∑ i : ZMod (m + 3), x i * (2 * x i - x (i - 1) - x (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [lap_mulVec]
  have h2 : ∑ i : ZMod (m + 3), x i * x (i - 1) = ∑ i : ZMod (m + 3), x i * x (i + 1) := by
    refine (Fintype.sum_equiv (Equiv.addRight (1 : ZMod (m + 3)))
      (fun i => x i * x (i + 1)) (fun i => x i * x (i - 1)) (fun i => ?_)).symm
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    exact mul_comm _ _
  have h3 : ∑ i : ZMod (m + 3), (x (i + 1)) ^ 2 = ∑ i : ZMod (m + 3), (x i) ^ 2 :=
    sum_shift_add (fun i => (x i) ^ 2)
  have e1 : ∑ i : ZMod (m + 3), x i * (2 * x i - x (i - 1) - x (i + 1))
      = 2 * (∑ i : ZMod (m + 3), (x i) ^ 2) - (∑ i : ZMod (m + 3), x i * x (i - 1))
        - ∑ i : ZMod (m + 3), x i * x (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i : ZMod (m + 3), (x i - x (i + 1)) ^ 2
      = (∑ i : ZMod (m + 3), (x i) ^ 2) + (∑ i : ZMod (m + 3), (x (i + 1)) ^ 2)
        - 2 * ∑ i : ZMod (m + 3), x i * x (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, e1, e2, h3, h2]
  ring

/-- The key spectral estimate: on the hyperplane `∑ x = 0`, the Laplacian quadratic form of
the cycle is bounded below by the Fiedler value times the squared norm. -/
