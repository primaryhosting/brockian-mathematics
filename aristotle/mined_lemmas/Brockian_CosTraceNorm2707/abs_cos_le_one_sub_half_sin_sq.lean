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

theorem abs_cos_le_one_sub_half_sin_sq (x : ℝ) :
    |Real.cos x| ≤ 1 - Real.sin x ^ 2 / 2 := by
  have h : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have := Real.sin_sq_add_cos_sq x; linarith
  rw [h]
  nlinarith [abs_nonneg (Real.cos x), sq_abs (Real.cos x), sq_nonneg (1 - |Real.cos x|)]

/--
**Cos Trace Norm 2707.**  For a finite spectrum `θ : n → ℝ`, the trace of `cos` of the
corresponding diagonal matrix is dominated in absolute value by the trace norm
`∑ i, |cos (θ i)|`, and this trace norm satisfies the sharpened dimension bound
`∑ i, |cos (θ i)| ≤ card n - (1/2) * ∑ i, sin (θ i) ^ 2`, which improves the trivial bound
`card n` by half the total "sine energy" of the spectrum.
-/
