/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The quadratic form of the cosine kernel `cos (θ i - θ j)` is a sum of two squares. -/

theorem cos_kernel_sum_abs_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ)
    (hA : (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).IsHermitian) :
    ∑ i, |hA.eigenvalues i| = (Fintype.card ι : ℝ) := by
  have hpos := cos_kernel_posSemidef θ
  have habs : ∀ i, |hA.eigenvalues i| = hA.eigenvalues i := fun i =>
    abs_of_nonneg (hpos.eigenvalues_nonneg i)
  have htr : (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).trace
      = ∑ i, (hA.eigenvalues i : ℝ) := hA.trace_eq_sum_eigenvalues
  simp only [habs]
  rw [← htr]
  simp [Matrix.trace, Matrix.diag, Finset.card_univ]

/-- Sharpness of the upper bound: for constant phases and the all-ones vector, the
cosine kernel form equals `(card ι) * ‖x‖²`. -/
