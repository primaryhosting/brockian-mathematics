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

lemma cos_two_pi_mul_le (N v : ℕ) (h1 : 1 ≤ v) (h2 : v < N) :
    Real.cos (2 * Real.pi * v / N) ≤ Real.cos (2 * Real.pi / N) := by
  have hN0 : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  have hpi := Real.pi_pos
  set w := min v (N - v) with hw
  have hw1 : 1 ≤ w := by simp [hw]; omega
  have hw2 : 2 * w ≤ N := by simp [hw]; omega
  have hcos : Real.cos (2 * Real.pi * v / N) = Real.cos (2 * Real.pi * w / N) := by
    rcases le_total v (N - v) with h | h
    · rw [hw, min_eq_left h]
    · rw [hw, min_eq_right h]
      have h3 : (2 * Real.pi * ((N - v : ℕ) : ℝ) / N) = 2 * Real.pi - 2 * Real.pi * v / N := by
        have h4 : ((N - v : ℕ) : ℝ) = (N : ℝ) - v := by
          have hle : v ≤ N := le_of_lt h2
          push_cast [hle]; ring
        rw [h4]; field_simp
      rw [h3, Real.cos_two_pi_sub]
  rw [hcos]
  have hw1' : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
  · rw [div_le_iff₀ hN]
    have : (2 : ℝ) * w ≤ N := by exact_mod_cast hw2
    nlinarith
  · rw [div_le_div_iff_of_pos_right hN]
    nlinarith

/-! ## The Laplacian of the cycle graph -/

section Cycle

variable {m : ℕ}

