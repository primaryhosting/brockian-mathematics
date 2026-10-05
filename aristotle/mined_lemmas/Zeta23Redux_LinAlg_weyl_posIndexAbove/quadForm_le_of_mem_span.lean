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

lemma quadForm_le_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {c : ℝ} (hc : ∀ i ∈ s, hM.eigenvalues i ≤ c)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j)) :
    quadForm M x ≤ c * ‖x‖ ^ 2 := by
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
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hc i hi) (by positivity)

/-- On the span of eigenvectors with eigenvalues `> c`, the quadratic form strictly exceeds
`c ‖x‖²` for nonzero `x`. -/
