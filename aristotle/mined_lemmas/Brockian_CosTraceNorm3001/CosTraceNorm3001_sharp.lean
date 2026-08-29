/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not permit a
-- module doc comment to precede the `import` commands; the text is otherwise verbatim.)

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

namespace Brockian

/-- Trace of a cosine-phase diagonal matrix times an arbitrary matrix:
`Tr (diag (cos θ) * A) = ∑ i, cos (θ i) * A i i`.

This is the basic computation underlying the `CosTraceNorm` family; it follows from
`Matrix.diagonal_mul` together with the definition of `Matrix.trace`. -/

theorem CosTraceNorm3001_sharp {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i, 0 ≤ A i i) :
    |Matrix.trace (Matrix.diagonal (fun i => Real.cos ((0 : n → ℝ) i)) * A)| = ∑ i, |A i i| := by
  rw [cos_diag_trace_eq]
  simp only [Pi.zero_apply, Real.cos_zero, one_mul]
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => hA i)]
  exact Finset.sum_congr rfl fun i _ => (abs_of_nonneg (hA i)).symm

end Brockian

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

