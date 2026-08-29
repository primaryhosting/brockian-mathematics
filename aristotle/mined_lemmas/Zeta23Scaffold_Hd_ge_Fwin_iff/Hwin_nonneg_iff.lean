/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma Hwin_nonneg_iff {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ Hwin lam ↔ 0 ≤ 6 * lam - 3 - lam ^ 2 := by
  rw [Hwin]
  rw [ge_iff_le, ← sub_nonneg]
  constructor
  · intro h
    have h' : 0 ≤ (2 - 1 / lam - lam / 3) * (3 * lam) := by positivity
    have : (2 - 1 / lam - lam / 3) * (3 * lam) = 6 * lam - 3 - lam ^ 2 := by
      field_simp; ring
    linarith [this ▸ h']
  · intro h
    have h3 : 0 < 3 * lam := by linarith
    have key : (2 - 1 / lam - lam / 3) * (3 * lam) = 6 * lam - 3 - lam ^ 2 := by
      field_simp; ring
    nlinarith [key, mul_pos h3 h3]

/-- The difference `H_d(λ) - F(λ)` factors as
`(6λ - 3 - λ²)(λ² - 3λ + 3) / (6λ(3 + λ²))`. -/
