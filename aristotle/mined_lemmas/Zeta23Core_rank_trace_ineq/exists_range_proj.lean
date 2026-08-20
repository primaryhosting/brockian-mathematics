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

theorem exists_range_proj (G : Matrix n n 𝕜) (hG : G.IsHermitian) :
    ∃ E : Matrix n n 𝕜, Eᴴ = E ∧ E * E = E ∧ E * G = G ∧
      (∀ B : Matrix n n 𝕜, B * G = 0 → B * E = 0) ∧ E.trace = (G.rank : 𝕜) := by
  classical
  set u : Matrix n n 𝕜 := (hG.eigenvectorUnitary : Matrix n n 𝕜) with hudef
  have hu : uᴴ * u = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self hG.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  set L : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hG.eigenvalues) with hL
  have hspec : G = u * L * uᴴ := by
    have := hG.spectral_theorem
    simpa [hudef, hL, Matrix.star_eq_conjTranspose] using this
  set D : Matrix n n 𝕜 := diagonal (fun i => if hG.eigenvalues i ≠ 0 then (1:𝕜) else 0) with hD
  have key : ∀ X : Matrix n n 𝕜, uᴴ * (u * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1; funext i; by_cases h : hG.eigenvalues i ≠ 0 <;> simp [h]
  have hDD : D * D = D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : hG.eigenvalues i ≠ 0 <;> simp [h]
  have hDL : D * L = L := by
    rw [hD, hL, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    by_cases h : hG.eigenvalues i ≠ 0
    · simp [h]
    · simp only [ne_eq, not_not] at h
      simp [h]
  refine ⟨u * D * uᴴ, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hDh]
  · simp only [Matrix.mul_assoc, key, ← Matrix.mul_assoc D D, hDD]
  · rw [hspec]
    simp only [Matrix.mul_assoc, key, ← Matrix.mul_assoc D L, hDL]
  · intro B hB
    rw [hspec] at hB
    have h1 : B * u * L = 0 := by
      have : (B * (u * L * uᴴ)) * u = 0 := by rw [hB, Matrix.zero_mul]
      simpa [Matrix.mul_assoc, hu] using this
    have h2 : B * u * D = 0 := by
      ext j i
      have hji := congrFun (congrFun h1 j) i
      rw [hL, Matrix.mul_diagonal] at hji
      rw [hD, Matrix.mul_diagonal]
      simp only [Matrix.zero_apply] at hji
      by_cases h : hG.eigenvalues i ≠ 0
      · simp only [h, ne_eq, not_false_eq_true, if_pos, Matrix.zero_apply]
        rcases mul_eq_zero.1 hji with h' | h'
        · simp [h']
        · simp only [Function.comp_apply, RCLike.ofReal_eq_zero] at h'
          exact absurd h' h
      · simp [h]
    calc B * (u * D * uᴴ) = (B * u * D) * uᴴ := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [h2, Matrix.zero_mul]
  · rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hD, Matrix.trace_diagonal,
      hG.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    simp [Finset.sum_ite, Finset.filter_not]

/-- For a Hermitian matrix `Q` there is an orthogonal projection `R` onto the span of the
eigenvectors with positive eigenvalue: its trace is the positive index of inertia, and `Q`
is negative semidefinite on the orthogonal complement of its range. -/
