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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

lemma qform_nonpos_of_inner_eq_zero {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) (h : ∀ i ∈ s, hM.eigenvalues i ≤ 0)
    {x : EuclideanSpace ℂ (Fin d)} (hx : ∀ i ∉ s, inner ℂ (hM.eigenvectorBasis i) x = 0) :
    qform M x ≤ 0 := by
  rw [qform_eq hM]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_nonpos_of_nonpos_of_nonneg (h i hi) (by positivity)
  · simp [hx i hi]

/-- On the span of eigenvectors with eigenvalues strictly above `c`, the quadratic form is
strictly above `c * ‖x‖ ^ 2` for nonzero vectors. -/
