import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

lemma mul_conjTranspose_of_decomp (hv : Orthonormal ℂ v)
    (hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k) :
    M * Mᴴ = ∑ i, ((s i : ℂ) ^ 2) • outer (u i) (u i) := by
  ext j a
  rw [Matrix.mul_apply]
  have expand : ∀ k, M j k * Mᴴ k a
      = ∑ i, ∑ l, ((s i : ℂ) * u i j * v i k) *
          ((s l : ℂ) * (starRingEnd ℂ) (u l a) * (starRingEnd ℂ) (v l k)) := by
    intro k
    rw [Matrix.conjTranspose_apply, hM, hM, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [← starRingEnd_apply, map_mul, Complex.conj_ofReal]
  simp only [expand]
  rw [Finset.sum_comm]
  have key : ∀ i : Fin r, ∑ k, ∑ l, ((s i : ℂ) * u i j * v i k) *
          ((s l : ℂ) * (starRingEnd ℂ) (u l a) * (starRingEnd ℂ) (v l k))
      = ((s i : ℂ) ^ 2) * (u i j * (starRingEnd ℂ) (u i a)) := by
    intro i
    rw [Finset.sum_comm]
    have step : ∀ l : Fin r, ∑ k, ((s i : ℂ) * u i j * v i k) *
          ((s l : ℂ) * (starRingEnd ℂ) (u l a) * (starRingEnd ℂ) (v l k))
        = ((s i : ℂ) * u i j * ((s l : ℂ) * (starRingEnd ℂ) (u l a))) *
            (if i = l then 1 else 0) := by
      intro l
      rw [← sum_conj_of_orthonormal hv i l, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [step]
    simp
    ring
  simp only [key]
  simp [outer, Matrix.sum_apply, smul_eq_mul]

