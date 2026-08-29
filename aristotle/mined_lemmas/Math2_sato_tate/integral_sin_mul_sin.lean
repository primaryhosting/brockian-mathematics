/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma integral_sin_mul_sin {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (0:ℝ)..π, Real.sin (((n : ℝ) + 1) * x) * Real.sin x) = 0 := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set G : ℝ → ℝ := fun x =>
    Real.sin ((n : ℝ) * x) / (2 * n) - Real.sin (((n : ℝ) + 2) * x) / (2 * ((n : ℝ) + 2)) with hG
  have hderiv : ∀ x : ℝ, HasDerivAt G (Real.sin (((n : ℝ) + 1) * x) * Real.sin x) x := by
    intro x
    have hl1 : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ))
    have hl2 : HasDerivAt (fun x : ℝ => ((n : ℝ) + 2) * x) ((n : ℝ) + 2) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ) + 2)
    have h1 : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * x))
        (Real.cos ((n : ℝ) * x) * (n : ℝ)) x := by
      simpa using (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x hl1
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (((n : ℝ) + 2) * x))
        (Real.cos (((n : ℝ) + 2) * x) * ((n : ℝ) + 2)) x := by
      simpa using (Real.hasDerivAt_sin (((n : ℝ) + 2) * x)).comp x hl2
    have h3 := (h1.div_const (2 * (n:ℝ))).sub (h2.div_const (2 * ((n : ℝ) + 2)))
    convert h3 using 1
    have key : Real.cos ((n:ℝ) * x) - Real.cos (((n:ℝ) + 2) * x)
        = 2 * Real.sin (((n:ℝ) + 1) * x) * Real.sin x := by
      have h := Real.cos_sub_cos ((n:ℝ) * x) (((n:ℝ) + 2) * x)
      have e1 : ((n:ℝ) * x + ((n:ℝ) + 2) * x) / 2 = ((n:ℝ) + 1) * x := by ring
      have e2 : ((n:ℝ) * x - ((n:ℝ) + 2) * x) / 2 = -x := by ring
      rw [h, e1, e2, Real.sin_neg]
      ring
    have hne1 : (n:ℝ) ≠ 0 := ne_of_gt hn0
    have r1 : Real.cos ((n:ℝ) * x) * (n:ℝ) / (2 * (n:ℝ)) = Real.cos ((n:ℝ) * x) / 2 := by
      field_simp
    have r2 : Real.cos (((n:ℝ) + 2) * x) * ((n:ℝ) + 2) / (2 * ((n:ℝ) + 2))
        = Real.cos (((n:ℝ) + 2) * x) / 2 := by
      have : ((n:ℝ) + 2) ≠ 0 := by positivity
      field_simp
    rw [r1, r2]
    linarith [key]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) 0 π)]
  have hs1 : Real.sin ((n : ℝ) * π) = 0 := Real.sin_nat_mul_pi n
  have hs2 : Real.sin (((n : ℝ) + 2) * π) = 0 := by
    have : ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact Real.sin_nat_mul_pi (n + 2)
  simp [hG, hs1, hs2]

