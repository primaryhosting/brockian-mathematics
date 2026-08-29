/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

namespace Brockian

open Complex

/-- The primitive `n`-th root of unity `exp (2πi / n)`, the rotation constant of the
regular `n`-gon. -/

lemma ngonRoot_pow_n : (ngonRoot n) ^ n = 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [ngonRoot, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [this]
  rw [show (2 : ℂ) * Real.pi * Complex.I = (2 * Real.pi : ℝ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I]
  simp

omit [NeZero n] in
