/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/

theorem norm_E_sub_one (x : ℝ) : ‖E x - 1‖ = 2 * |Real.sin (x / 2)| := by
  have h1 : E x - 1 = ⟨Real.cos x - 1, Real.sin x⟩ := by
    rw [E, Complex.exp_mul_I]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h2 : Real.cos (2 * (x / 2)) = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 :=
      Real.cos_two_mul' _
    rw [show 2 * (x / 2) = x by ring] at h2
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [h1, Complex.norm_def, Complex.normSq_mk]
  have key : (Real.cos x - 1) * (Real.cos x - 1) + Real.sin x * Real.sin x
      = (2 * |Real.sin (x / 2)|) ^ 2 := by
    rw [hc, hs, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [key]
  exact Real.sqrt_sq (by positivity)

