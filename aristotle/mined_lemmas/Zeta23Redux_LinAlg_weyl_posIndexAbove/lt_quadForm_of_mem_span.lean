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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The Rayleigh quadratic form of a matrix `M` at a vector `x` of Euclidean space:
`Re ⟪x, M x⟫`. -/

lemma lt_quadForm_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {c : ℝ} (hc : ∀ i ∈ s, c < hM.eigenvalues i)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j))
    (hx0 : x ≠ 0) :
    c * ‖x‖ ^ 2 < quadForm M x := by
  have hzero : ∀ i ∉ s, (inner ℂ (hM.eigenvectorBasis i) x : ℂ) = 0 := fun i hi =>
    inner_eq_zero_of_mem_span hM s hx hi
  have h1 : quadForm M x = ∑ i ∈ s, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    rw [quadForm_eq_sum hM]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp [hzero i hi]
  have h2 : ‖x‖ ^ 2 = ∑ i ∈ s, ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    rw [norm_sq_eq_sum hM x]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp [hzero i hi]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have hex : ∃ i ∈ s, 0 < ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have : ‖x‖ ^ 2 = 0 := by
      rw [h2]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := hcon i hi
      have h0 : (0:ℝ) ≤ ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by positivity
      linarith
    exact absurd this (ne_of_gt hpos)
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i hi => mul_le_mul_of_nonneg_right (le_of_lt (hc i hi))
    (by positivity)) ?_
  obtain ⟨i, hi, hip⟩ := hex
  exact ⟨i, hi, by nlinarith [hc i hi]⟩

/-- The dimension of the span of a subfamily of the eigenbasis. -/
