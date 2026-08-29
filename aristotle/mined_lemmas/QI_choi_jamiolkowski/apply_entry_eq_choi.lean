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

lemma apply_entry_eq_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ)
    (a b : m) : Φ X a b = ∑ i, ∑ j, X i j * choiMatrix Φ (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [show ∀ i j, Matrix.single i j (X i j) = X i j • Matrix.single (n := n) i j 1 from
      fun i j => by simp [Matrix.smul_single], map_sum, map_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, choiMatrix, Matrix.of_apply]

/-- The block-diagonal ampliation `1ₖ ⊗ V` of a Kraus operator. -/
