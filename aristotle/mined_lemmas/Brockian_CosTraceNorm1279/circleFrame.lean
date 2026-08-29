/-
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The circular (cosine) Gram matrix of a family of angles `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

noncomputable def circleFrame (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k i => if k = 0 then Real.cos (θ i) else Real.sin (θ i)

/-- The cosine Gram matrix is the Gram matrix of the unit vectors on the circle. -/
