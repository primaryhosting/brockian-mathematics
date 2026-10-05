/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The trace norm (Schatten `1`-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

theorem CosTraceNorm1597_quadratic (hA : A.IsHermitian) (t : ℝ) :
    ‖(cfc (fun x : ℝ => Real.cos (t * x)) A).trace - (Fintype.card n : ℂ)‖
      ≤ t ^ 2 / 2 * hsNormSq hA := by
  have hcard : ((Fintype.card n : ℂ)) = ((∑ _i : n, (1 : ℝ) : ℝ) : ℂ) := by
    simp [Finset.card_univ]
  rw [trace_cos_smul hA, hcard, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  calc |∑ i, (Real.cos (t * hA.eigenvalues i) - 1)|
      ≤ ∑ i, |Real.cos (t * hA.eigenvalues i) - 1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, t ^ 2 / 2 * (hA.eigenvalues i) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := abs_cos_sub_one_le_sq (t * hA.eigenvalues i)
        calc |Real.cos (t * hA.eigenvalues i) - 1| ≤ (t * hA.eigenvalues i) ^ 2 / 2 := this
          _ = t ^ 2 / 2 * (hA.eigenvalues i) ^ 2 := by ring
    _ = t ^ 2 / 2 * hsNormSq hA := by rw [hsNormSq, Finset.mul_sum]

end Brockian

