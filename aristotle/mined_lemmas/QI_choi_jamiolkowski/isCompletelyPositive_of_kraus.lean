import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/

lemma isCompletelyPositive_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : HasKrausRepresentation Φ) : IsCompletelyPositive Φ := by
  obtain ⟨V, hV⟩ := h
  intro k _ _ X hX
  have key : ampliation k Φ X
      = ∑ c, krausAmp k (V c) * X * (krausAmp k (V c))ᴴ := by
    ext p q
    simp only [ampliation, Matrix.of_apply, hV, Matrix.sum_apply, kraus_term_entry]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 := sum_prod_collapse (n := n) X p.1 q.1 (fun i => V c p.2 i)
      (fun j => (starRingEnd ℂ) (V c q.2 j))
    simpa only [krausAmp, Matrix.of_apply, apply_ite (starRingEnd ℂ), map_zero] using h1.symm
  rw [key]
  exact posSemidef_sum _ _ fun c _ => hX.mul_mul_conjTranspose_same _

omit [Fintype m] [DecidableEq m] in
/-- A completely positive map has a positive semidefinite Choi matrix:
the Choi matrix is the image of the (unnormalized) maximally entangled state. -/
