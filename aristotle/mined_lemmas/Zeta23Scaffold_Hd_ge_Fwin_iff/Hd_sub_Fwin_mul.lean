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

theorem Hd_sub_Fwin_mul (lam : ℝ) (hlam : 0 < lam) :
    (6 * lam * (3 + lam ^ 2)) * (Hd lam - Fwin lam)
      = (6 * lam - 3 - lam ^ 2) * (lam ^ 2 - 3 * lam + 3) := by
  have h1 : lam ≠ 0 := ne_of_gt hlam
  have h2 : (1 : ℝ) + lam ^ 2 / 3 ≠ 0 := by positivity
  simp only [Hd, Fwin, Hwin]
  field_simp
  ring

/-- `H_d(λ) ≥ F(λ)` if and only if `H(λ) ≥ 0`, for `0 < λ ≤ 1`
(preprint eq. (1.3), third line, first equivalence).

The hypothesis `lam ≤ 1` is included as stated in the target, but it turns out to be
unnecessary: the equivalence holds for every `λ > 0`. -/
