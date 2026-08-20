import Mathlib

/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
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

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/

theorem Hwin_nonneg_iff (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have : Hwin lam = (6 * lam - 3 - lam ^ 2) / (3 * lam) := by
    unfold Hwin; field_simp; ring
  rw [this, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Unconditional form (valid for all `λ > 0`): `F(λ) ≤ H_d(λ) ↔ 0 ≤ H(λ)`. -/
