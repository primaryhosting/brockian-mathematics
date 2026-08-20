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

lemma cycle_fiedler_value_aux (m : ℕ) :
    IsLeast {r : ℝ | ∃ x : ZMod (m + 3) → ℝ, x ≠ 0 ∧ (∑ i : ZMod (m + 3), x i = 0) ∧
        r = (x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)) / (∑ i : ZMod (m + 3), x i ^ 2)}
      (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))) ∧
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : ZMod (m + 3) → ℝ, v ≠ 0 ∧
        (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))) := by
  set mu : ℝ := 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))
  have hmupos : 0 < mu := fiedler_pos
  have hv2 : 0 < ∑ i : ZMod (m + 3), (fiedlerVec m i) ^ 2 := sum_sq_pos fiedlerVec_ne_zero
  have hlower : ∀ x : ZMod (m + 3) → ℝ, (∑ i : ZMod (m + 3), x i = 0) →
      mu * (∑ i : ZMod (m + 3), (x i) ^ 2) ≤ x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) := by
    intro x hsum
    rw [lap_quadForm]
    exact cycle_quad_lower x hsum
  have hQv : fiedlerVec m ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fiedlerVec m)
      = mu * ∑ i : ZMod (m + 3), (fiedlerVec m i) ^ 2 := by
    rw [fiedlerVec_lap, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
  constructor
  · constructor
    · refine ⟨fiedlerVec m, fiedlerVec_ne_zero, fiedlerVec_sum, ?_⟩
      rw [hQv, mul_div_assoc, div_self (ne_of_gt hv2), mul_one]
    · rintro r ⟨x, hx, hxsum, rfl⟩
      have hx2 : 0 < ∑ i : ZMod (m + 3), (x i) ^ 2 := sum_sq_pos hx
      rw [le_div_iff₀ hx2]
      exact hlower x hxsum
  · constructor
    · exact ⟨ne_of_gt hmupos, fiedlerVec m, fiedlerVec_ne_zero, fiedlerVec_lap⟩
    · rintro nu ⟨hnu0, v, hv, hlap⟩
      have hvsum : ∑ i : ZMod (m + 3), v i = 0 := by
        have hz : ∑ i : ZMod (m + 3), ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v) i = 0 := by
          have hpt : ∀ i : ZMod (m + 3), ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v) i
              = 2 * v i - v (i - 1) - v (i + 1) := fun i => lap_mulVec v i
          rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib,
            Finset.sum_sub_distrib, sum_shift_sub (fun i => v i), sum_shift_add (fun i => v i),
            ← Finset.mul_sum]
          ring
        rw [hlap] at hz
        have hz2 : nu * ∑ i : ZMod (m + 3), v i = 0 := by
          rw [← hz, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]
        exact (mul_eq_zero.mp hz2).resolve_left hnu0
      have hv2' : 0 < ∑ i : ZMod (m + 3), (v i) ^ 2 := sum_sq_pos hv
      have hQ : v ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v)
          = nu * ∑ i : ZMod (m + 3), (v i) ^ 2 := by
        rw [hlap, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
      have hkey := hlower v hvsum
      rw [hQ] at hkey
      exact le_of_mul_le_mul_right (by linarith) hv2'

end Cycle

/-- **The Fiedler value (algebraic connectivity) of the cycle graph `C n`,
for `n ≥ 3`, equals `2 - 2 cos (2π/n)`.**

Two equivalent formulations are given:
* it is the minimum of the Rayleigh quotient of the Laplacian over nonzero vectors orthogonal
  to the all-ones vector (the variational characterization of the second smallest Laplacian
  eigenvalue);
* it is the smallest nonzero eigenvalue of the Laplacian matrix of `C n`. -/
