/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Real

namespace Frontier

/-- A Boolean spin variable read as a real number `±1`. -/

lemma sinh_two_onsagerKc : Real.sinh (2 * onsagerKc) = 1 := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2
  have hs0 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpos : (0:ℝ) < 1 + Real.sqrt 2 := by linarith
  have h2K : 2 * onsagerKc = Real.log (1 + Real.sqrt 2) := by
    unfold onsagerKc; ring
  rw [h2K, Real.sinh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
  have hne : (1 + Real.sqrt 2) ≠ 0 := by positivity
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 := by
    field_simp
    nlinarith
  rw [hinv]; ring

/-- The Onsager integrand is bounded below by `(sinh 2K - 1)²`; in particular it is nonnegative
for all `K ≥ 0`, and it can only vanish where `sinh (2K) = 1`. -/
