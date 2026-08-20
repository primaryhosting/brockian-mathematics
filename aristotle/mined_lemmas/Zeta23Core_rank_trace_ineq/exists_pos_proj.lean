/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of (strictly) positive
eigenvalues.  (For non-Hermitian matrices the value is set to `0`.) -/

theorem exists_pos_proj (Q : Matrix n n 𝕜) (hQ : Q.IsHermitian) :
    ∃ R : Matrix n n 𝕜, Rᴴ = R ∧ R * R = R ∧ R.trace = ((posIndex Q : ℕ) : 𝕜) ∧
      (-((1 - R) * Q * (1 - R))).PosSemidef := by
  classical
  set u : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hudef
  have hu : uᴴ * u = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self hQ.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have hu2 : u * uᴴ = 1 := (mul_eq_one_comm_of_card_eq n n 𝕜 rfl).mp hu
  set L : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hQ.eigenvalues) with hL
  have hspec : Q = u * L * uᴴ := by
    have := hQ.spectral_theorem
    simpa [hudef, hL, Matrix.star_eq_conjTranspose] using this
  set D : Matrix n n 𝕜 := diagonal (fun i => if 0 < hQ.eigenvalues i then (1:𝕜) else 0) with hD
  have key : ∀ X : Matrix n n 𝕜, uᴴ * (u * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1; funext i; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
  have hDD : D * D = D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
  refine ⟨u * D * uᴴ, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hDh]
  · simp only [Matrix.mul_assoc, key, ← Matrix.mul_assoc D D, hDD]
  · rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hD, Matrix.trace_diagonal,
      posIndex_eq Q hQ]
    simp
  · have hone : (1 : Matrix n n 𝕜) - u * D * uᴴ = u * (1 - D) * uᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu2]
    rw [hone, hspec]
    have hprod : u * (1 - D) * uᴴ * (u * L * uᴴ) * (u * (1 - D) * uᴴ)
        = u * ((1 - D) * L * (1 - D)) * uᴴ := by
      simp only [Matrix.mul_assoc, key]
    rw [hprod]
    have hone' : (1 : Matrix n n 𝕜) - D = diagonal (fun i =>
        if 0 < hQ.eigenvalues i then (0:𝕜) else 1) := by
      rw [hD]
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
      · simp [hij]
    have hdiag : (1 - D) * L * (1 - D)
        = diagonal (fun i =>
            if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i)) := by
      rw [hone', hL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext i; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
    rw [hdiag]
    have hnegd : -(u * (diagonal (fun i =>
          if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i))) * uᴴ)
        = u * (diagonal (fun i =>
          -(if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i)))) * uᴴ := by
      rw [← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hnegd]
    have hpsd : (diagonal (fun i =>
        -(if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i)))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      by_cases h : 0 < hQ.eigenvalues i
      · simp [h]
      · simp only [h, if_false]
        push_neg at h
        rw [← RCLike.ofReal_neg]
        exact RCLike.ofReal_nonneg.mpr (by linarith)
    simpa using hpsd.mul_mul_conjTranspose_same u

/-- Rank–trace inequality (preprint Lemma 3.2).  If `P` is positive semidefinite of rank at
most `r`, `Q` is Hermitian with at most `b` positive eigenvalues and `c > 0`, then
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`, where `‖M‖_F² = Re tr (Mᴴ M)`. -/
