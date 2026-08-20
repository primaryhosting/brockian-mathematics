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

Target: `Zeta23Redux.LinAlg.weyl_posIndexAbove`

For a Hermitian matrix `A` over `ℂ` of size `Fin d` we define

* `posIndex hA`, the number of strictly positive eigenvalues of `A`;
* `posIndexAbove hA θ`, the number of eigenvalues of `A` strictly above `θ`.

The main result `weyl_posIndexAbove` is Weyl's monotonicity statement: if all eigenvalues of a
Hermitian perturbation `E` are bounded in absolute value by `θ`, then
`posIndexAbove (A + E) θ ≤ posIndex A`.

The proof is the Courant–Fischer/interlacing argument in its subspace form: the span of the
eigenvectors of `A + E` with eigenvalue `> θ` intersects trivially the span of the eigenvectors of
`A` with eigenvalue `≤ 0`, because on the first subspace the quadratic form of `A + E` is `> θ‖x‖²`
while on the second one it is `≤ 0 + θ‖x‖²`.  Comparing dimensions gives the claim.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma quadForm_gt (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (c : ℝ) (hx : x ≠ 0)
    (h : ∀ i, inner ℂ (hM.eigenvectorBasis i) x ≠ 0 → c < hM.eigenvalues i) :
    c * ‖x‖ ^ 2 < (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ).re := by
  rw [quadForm_eq_sum hM x, ← sum_norm_inner_sq hM x, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ?_
  · rcases eq_or_ne (inner ℂ (hM.eigenvectorBasis i) x) 0 with h0 | h0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (h i h0).le (by positivity)
  · have hne : ∃ i, inner ℂ (hM.eigenvectorBasis i) x ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      have hsum := sum_norm_inner_sq hM x
      simp [hc] at hsum
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_right (h i hi) (by positivity)⟩

end Quadratic

section Span

/-- A vector orthogonal to a spanning family is orthogonal to everything in the span. -/
