import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The (complex) diagonal matrix whose diagonal entries are `cos (θ i)`.  Equivalently, this is
`cos A` for the real diagonal matrix `A = diagonal θ`, whose spectrum is `θ`. -/

noncomputable def cosDiag {n : Type*} [Fintype n] [DecidableEq n] (θ : n → ℝ) :
    Matrix n n ℂ := Matrix.diagonal (fun i => (Real.cos (θ i) : ℂ))

/-- The trace norm (Schatten 1-norm) of `cosDiag θ`: the sum of the absolute values of its
eigenvalues `cos (θ i)`. -/
