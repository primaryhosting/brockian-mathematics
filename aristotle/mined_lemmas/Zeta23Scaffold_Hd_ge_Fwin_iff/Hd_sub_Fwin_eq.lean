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

lemma Hd_sub_Fwin_eq {lam : ℝ} (hlam : 0 < lam) :
    Hd lam - Fwin lam =
      (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) / (6 * lam * (3 + lam ^ 2)) := by
  have h1 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := by positivity
  have h2 : lam ≠ 0 := ne_of_gt hlam
  have h3 : (3 : ℝ) + lam ^ 2 ≠ 0 := by positivity
  rw [Hd, Fwin, Hwin]
  field_simp
  ring

/-- `H_d(λ) ≥ F(λ)` iff `H(λ) ≥ 0`, for `0 < λ ≤ 1`. -/
