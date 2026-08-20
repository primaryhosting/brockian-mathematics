import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
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

namespace Math2

open Matrix

variable {n : ℕ}

/-- The standard symplectic form on `ℝ ^ (2 * n)`, with `ℝ ^ (2 * n)` modelled as functions
`(Fin n ⊕ Fin n) → ℝ`: the coordinates indexed by `Sum.inl i` are the positions `qᵢ` and the
coordinates indexed by `Sum.inr i` are the momenta `pᵢ`. -/

lemma rows_omegaForm {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (i₀ : Fin n) :
    ∑ j : Fin n, (A (Sum.inl i₀) (Sum.inr j) * A (Sum.inr i₀) (Sum.inl j)
      - A (Sum.inl i₀) (Sum.inl j) * A (Sum.inr i₀) (Sum.inr j)) = -1 := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.1 hA) (Sum.inl i₀)) (Sum.inr i₀)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_sub_distrib] at h ⊢
  linarith [h]

/-- If the image of the ball of radius `r` under the affine map `x ↦ A *ᵥ x + b` lies in the
cylinder of radius `R`, then each of the two relevant rows `A a` of `A` satisfies
`r ^ 2 * ‖A a‖ ^ 2 ≤ R ^ 2`. -/
