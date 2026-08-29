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

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The "cosine trace" of a Hermitian matrix `A`: the trace of `cos A`, computed
through the spectral decomposition as the sum of `cos` of the eigenvalues. -/

noncomputable def hsNormSq {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, (hA.eigenvalues i) ^ 2

/-- Pointwise bound: `1 - cos x ≤ |x|` for every real `x`. -/
