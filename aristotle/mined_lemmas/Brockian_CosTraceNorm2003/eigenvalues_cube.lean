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

lemma eigenvalues_cube {A : Matrix n n ℂ} (hA : A.IsHermitian) {t : ℝ}
    (h : A * A * A = (t : ℂ) • A) (i : n) :
    (hA.eigenvalues i) ^ 3 = t * hA.eigenvalues i := by
  set w : n → ℂ := ⇑(hA.eigenvectorBasis i) with hw
  set l := hA.eigenvalues i with hl
  have hAw : A *ᵥ w = l • w := hA.mulVec_eigenvectorBasis i
  have hwne : w ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i
  have e1 : A *ᵥ (A *ᵥ (A *ᵥ w)) = (l ^ 3) • w := by
    simp only [hAw, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, ← mul_assoc, h,
    Matrix.smul_mulVec, hAw] at e1
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hwne
  have hc := congrFun e1 j
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] at hc
  have h2 : ((t * l : ℝ) : ℂ) = ((l ^ 3 : ℝ) : ℂ) :=
    mul_right_cancel₀ hj (by push_cast at hc ⊢; linear_combination hc)
  exact_mod_cast h2.symm

/-- The trace of `A * A` is the sum of the squares of the eigenvalues of `A`. -/
