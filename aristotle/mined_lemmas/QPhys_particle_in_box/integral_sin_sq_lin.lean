/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain comment and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Real

/-- The (unnormalized-constant times) `n`-th stationary state of the infinite square
well of width `L`: `ψ n x = c * sin (n π x / L)`. -/

lemma integral_sin_sq_lin (k : ℝ) (hk : k ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.sin (k * x) ^ 2
      = (b / 2 - Real.sin (2 * k * b) / (4 * k)) - (a / 2 - Real.sin (2 * k * a) / (4 * k)) := by
  have H : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => x / 2 - Real.sin (2 * k * x) / (4 * k)) (Real.sin (k * x) ^ 2) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => 2 * k * x) (2 * k) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 * k))
    have h3 := (((hasDerivAt_id x).div_const 2).sub ((h1.sin).div_const (4 * k)))
    have hc : Real.cos (2 * k * x) = 1 - 2 * Real.sin (k * x) ^ 2 := by
      rw [show (2 : ℝ) * k * x = 2 * (k * x) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (k * x)]
    convert h3 using 1
    rw [hc]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => H x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- The states `ψ_n` are normalized on the well `[0, L]`. -/
