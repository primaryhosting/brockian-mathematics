import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace Chem

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma Dv_eq (l : Fin 10) :
    Dv l = ((2 * Real.cos (2 * Real.pi * (l : ℕ) / 10) : ℝ) : ℂ) := by
  have hE : E l = Complex.exp ((2 * Real.pi * (l : ℕ) / 10 : ℝ) * Complex.I) := by
    rw [E, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hEn : E (-l) = Complex.exp (-((2 * Real.pi * (l : ℕ) / 10 : ℝ) * Complex.I)) := by
    rw [E_neg, hE, ← Complex.exp_neg]
  rw [Dv, hE, hEn]
  push_cast
  rw [Complex.two_cos]
  ring_nf

/-- **Hückel theory for the cycle `C₁₀`**: the characteristic polynomial of the adjacency
matrix of the cycle graph on 10 vertices factors as `∏ (X - 2cos(2πk/10))`, i.e. the
adjacency eigenvalues of `C₁₀` are exactly `2 cos(2πk/10)` for `k = 0, …, 9`. -/
