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

/-- The cosine Gram matrix of a family of angles: `C θ i j = cos (θ i - θ j)`,
the Gram matrix of the unit vectors `(cos (θ i), sin (θ i))` in the plane. -/

lemma cosGram_quadratic_form (n : ℕ) (θ : Fin n → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (Matrix.mulVec (cosGram n θ) x)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, cosGram, Matrix.of_apply, Real.cos_sub, pow_two,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The cosine Gram matrix is symmetric (Hermitian over `ℝ`). -/
