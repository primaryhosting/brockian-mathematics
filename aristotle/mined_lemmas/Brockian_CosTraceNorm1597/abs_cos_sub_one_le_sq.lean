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

lemma abs_cos_sub_one_le_sq (y : ℝ) : |Real.cos y - 1| ≤ y ^ 2 / 2 := by
  have h1 : Real.cos y ≤ 1 := Real.cos_le_one y
  have h2 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  rw [abs_le]
  constructor <;> linarith

/-- **Cos Trace Norm 1597.**

For a Hermitian matrix `A` and a real parameter `t`, the trace of `cos (t A)` (defined by
the continuous functional calculus) deviates from the trace of the identity by at most
`|t|` times the trace norm of `A`:
`‖Tr cos (t A) - n‖ ≤ |t| · ‖A‖₁`. -/
