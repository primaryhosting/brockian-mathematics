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

import Mathlib
/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module doc comment, so the
-- header block above appears immediately after the single required import.)

open scoped BigOperators
open scoped Real

namespace Brockian

open Matrix

/-! ## The trace norm of a Hermitian matrix -/

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

lemma sum_sq_eigenvalues_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) {r : ℝ}
    (htr : (A * A).trace = (r : ℂ)) : ∑ i, (hA.eigenvalues i) ^ 2 = r := by
  have h1 := trace_mul_self_eq_sum_sq_eigenvalues hA
  rw [htr] at h1
  have h2 : ((r : ℝ) : ℂ) = ((∑ i, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2.symm

/-- Key structural computation: a Hermitian matrix `A` with `A³ = s² A` and `tr(A²) = 2 s²`
(for `s ≥ 0`) has trace norm `2 s`. -/
