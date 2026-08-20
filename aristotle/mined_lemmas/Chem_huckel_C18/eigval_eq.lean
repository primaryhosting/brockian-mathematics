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

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/

lemma eigval_eq (k : ZMod 18) :
    eigval k = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 18) : ℝ) : ℂ) := by
  have hk : (((k.val : ℤ)) : ZMod 18) = k := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  have h1 : psi k = Complex.exp (2 * Real.pi * Complex.I * (k.val : ℤ) / 18) := by
    rw [psi, ← hk, ZMod.stdAddChar_coe]
    norm_num
  have h2 : psi (-k) = Complex.exp (2 * Real.pi * Complex.I * (-(k.val : ℤ)) / 18) := by
    rw [psi, show -k = (((-(k.val : ℤ)) : ℤ) : ZMod 18) by push_cast [hk]; ring,
      ZMod.stdAddChar_coe]
    norm_num
  have h3 : ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 18) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * (k.val : ℝ) / 18 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [eigval, h1, h2, h3, Complex.two_cos]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- **Hückel theory for `C₁₈`.** The spectrum of the adjacency matrix of the cycle graph
`C₁₈` is exactly the set of numbers `2 cos (2 π k / 18)` for `k = 0, …, 17`. -/
