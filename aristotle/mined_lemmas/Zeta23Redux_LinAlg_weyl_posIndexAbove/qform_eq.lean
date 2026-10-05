/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_eq {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform A x = ∑ i, hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 := by
  have key : ∀ a b : ℝ, (a : ℂ) * (b : ℂ) = ((a * b : ℝ) : ℂ) := by
    intro a b; push_cast; ring
  have hsym := Matrix.isHermitian_iff_isSymmetric.1 hA
  have h := hA.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin A x)
  have h2 : ∀ i : Fin d,
      inner ℂ x (hA.eigenvectorBasis i) * inner ℂ (hA.eigenvectorBasis i)
        (Matrix.toEuclideanLin A x)
      = ((hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h3 : inner ℂ (hA.eigenvectorBasis i) (Matrix.toEuclideanLin A x)
        = (hA.eigenvalues i : ℂ) * inner ℂ (hA.eigenvectorBasis i) x := by
      rw [← hsym (hA.eigenvectorBasis i) x, toEuclideanLin_eigenvectorBasis hA i,
        inner_smul_left]
      simp
    have hc : inner ℂ x (hA.eigenvectorBasis i)
        = (starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis i) x) :=
      (inner_conj_symm _ _).symm
    rw [h3, hc, ← mul_assoc, mul_comm ((starRingEnd ℂ) _) _, mul_assoc, RCLike.conj_mul,
      ← RCLike.ofReal_pow]
    exact key _ _
  rw [Finset.sum_congr rfl (fun i _ => h2 i)] at h
  have h4 := congrArg RCLike.re h
  simp only [map_sum] at h4
  rw [qform, ← h4]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- Parseval's identity in the eigenbasis. -/
