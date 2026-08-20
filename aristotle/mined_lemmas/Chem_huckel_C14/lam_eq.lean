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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₄`, viewed with vertex set `ZMod 14`
(which is definitionally `Fin 14`). -/

lemma lam_eq (k : ZMod 14) :
    lam k = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k.val : ℝ) / 14 with ht
  have hchk : ch k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ch, zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h2 : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show (t : ℂ) * Complex.I + -(t : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero]
  have hinv : ch (-k) = Complex.exp (-(t : ℂ) * Complex.I) := by
    have h1 : ch k * ch (-k) = 1 := ch_neg_mul_self k
    rw [hchk] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  rw [lam, hchk, hinv, ← Complex.two_cos, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

/-- **Hückel spectrum of `C₁₄`.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₄` are exactly the numbers `2 * cos (2 * π * k / 14)` for `k = 0, 1, …, 13`. -/
