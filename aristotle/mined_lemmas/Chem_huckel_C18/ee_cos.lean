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

namespace Chem

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma ee_cos (c : ℕ) :
    ee (c : ℤ) + ee (-(c : ℤ)) = 2 * ((Real.cos (2 * Real.pi * c / 18) : ℝ) : ℂ) := by
  have h1 : ee (c : ℤ) = Complex.exp (((2 * Real.pi * c / 18 : ℝ) : ℂ) * Complex.I) := by
    rw [ee, zpow_natCast, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : ee (-(c : ℤ)) = Complex.exp (-(((2 * Real.pi * c / 18 : ℝ) : ℂ) * Complex.I)) := by
    rw [ee, _root_.zpow_neg, zpow_natCast, zeta, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [h1, h2, Complex.exp_mul_I,
    show (-((((2 * Real.pi * c / 18 : ℝ)) : ℂ) * Complex.I))
        = ((-(2 * Real.pi * c / 18 : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

