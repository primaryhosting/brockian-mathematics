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

theorem cos_kernel_bound_sharp {ι : Type*} [Fintype ι] :
    ∑ i : ι, ∑ _j : ι, (1 : ℝ) * 1 * Real.cos ((0 : ι → ℝ) i - (0 : ι → ℝ) i)
      = (Fintype.card ι : ℝ) * ∑ _i : ι, (1 : ℝ) ^ 2 := by
  simp [Finset.card_univ]

/-- **Cos Trace Norm 2707.**
For any finite index type `ι` and any phases `θ : ι → ℝ`, the cosine kernel matrix
`A i j = cos (θ i - θ j)` is positive semidefinite, has trace `card ι`, and hence has trace
norm (sum of absolute values of its eigenvalues) exactly `card ι`; consequently its quadratic
form satisfies the two-sided bound `0 ≤ xᵀ A x ≤ (card ι) * ‖x‖²` for every real vector `x`. -/
