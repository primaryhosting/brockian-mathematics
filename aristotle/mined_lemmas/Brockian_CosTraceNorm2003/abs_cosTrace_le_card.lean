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

/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values of
its eigenvalues. -/

theorem abs_cosTrace_le_card {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    |cosTrace hA| ≤ (Fintype.card n : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- **Cos Trace Norm 2003.**  For a Hermitian matrix `A` of size `n`, the defect
`n - Tr cos A` is nonnegative and is dominated both by the trace norm `‖A‖₁` of `A`
and by half of its squared Hilbert–Schmidt norm. -/
