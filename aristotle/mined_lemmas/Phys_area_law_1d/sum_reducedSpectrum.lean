/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

namespace Phys

open Matrix
open scoped ComplexOrder

/-- Von Neumann entropy of a spectrum `p` (a list of eigenvalues of a density matrix). -/

lemma sum_reducedSpectrum {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (hM : ∑ a : A, ∑ b : B, ‖M a b‖ ^ 2 = 1) :
    ∑ a : A, reducedSpectrum M a = 1 := by
  have h1 : (M * Mᴴ).trace = ∑ a : A, ((reducedSpectrum M a : ℝ) : ℂ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues (Matrix.isHermitian_mul_conjTranspose_self M)
  have h2 : (M * Mᴴ).trace = ((∑ a : A, ∑ b : B, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hM, h1] at h2
  have h3 : ((∑ a : A, reducedSpectrum M a : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast
    simpa using h2
  exact_mod_cast h3

/-- The number of nonzero elements of the reduced spectrum is the rank of `M`. -/
