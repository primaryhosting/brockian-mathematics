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

lemma choiMatrix_posSemidef_of_completelyPositive
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (h : IsCompletelyPositive Φ) :
    (choiMatrix Φ).PosSemidef := by
  set A : Matrix Unit (n × n) ℂ := Matrix.of fun _ p => if p.1 = p.2 then 1 else 0 with hA
  set Om : Matrix (n × n) (n × n) ℂ := Aᴴ * A with hOm
  have hOmPSD : Om.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have key : ampliation n Φ Om = choiMatrix Φ := by
    ext p q
    have hblock : (Matrix.of fun i j => Om (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 (1 : ℂ) := by
      ext i j
      simp only [hOm, hA, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
        Matrix.single_apply, Finset.univ_unique, Finset.sum_singleton, RCLike.star_def]
      split_ifs <;> simp_all
    simp [ampliation, choiMatrix, hblock]
  rw [← key]
  exact h n Om hOmPSD

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite; equivalently, iff it
admits a Kraus representation. -/
