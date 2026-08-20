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

lemma sq_sinh_sub_one_le_onsagerIntegrand {K : ℝ} (hK : 0 ≤ K) (θ₁ θ₂ : ℝ) :
    (Real.sinh (2 * K) - 1) ^ 2 ≤ onsagerIntegrand K θ₁ θ₂ := by
  have hs : 0 ≤ Real.sinh (2 * K) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hc : Real.cosh (2 * K) ^ 2 = Real.sinh (2 * K) ^ 2 + 1 := by
    rw [Real.cosh_sq']; ring
  have h1 : Real.cos θ₁ ≤ 1 := Real.cos_le_one θ₁
  have h2 : Real.cos θ₂ ≤ 1 := Real.cos_le_one θ₂
  unfold onsagerIntegrand
  nlinarith [mul_nonneg hs (sub_nonneg.mpr h1), mul_nonneg hs (sub_nonneg.mpr h2)]

/-- The Onsager integrand vanishes for some momenta iff `K` is the critical coupling. -/
