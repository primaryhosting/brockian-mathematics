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

lemma choiMatrix_posSemidef_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : HasKrausRepresentation Φ) : (choiMatrix Φ).PosSemidef := by
  obtain ⟨V, hV⟩ := h
  set A : Matrix (n × m) (n × m) ℂ :=
    Matrix.of fun c q => (starRingEnd ℂ) (V c q.2 q.1) with hA
  have key : choiMatrix Φ = Aᴴ * A := by
    ext p q
    rw [Matrix.mul_apply]
    simp only [choiMatrix, Matrix.of_apply, hV, Matrix.sum_apply, kraus_term_entry,
      Matrix.conjTranspose_apply, hA]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  rw [key]
  exact Matrix.posSemidef_conjTranspose_mul_self A

/-- If the Choi matrix is positive semidefinite then `Φ` has a Kraus representation. -/
