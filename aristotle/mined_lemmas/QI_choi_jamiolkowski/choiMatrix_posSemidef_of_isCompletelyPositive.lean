/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/

theorem choiMatrix_posSemidef_of_isCompletelyPositive (h : IsCompletelyPositive Φ) :
    (choiMatrix Φ).PosSemidef := by
  classical
  set Ω : Matrix Unit (n × n) ℂ := Matrix.of fun _ x => if x.1 = x.2 then 1 else 0 with hΩ
  have hPSD : (Ωᴴ * Ω).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Ω
  have harg : ∀ p q : n,
      (Matrix.of fun i j => (Ωᴴ * Ω) (i, p) (j, q)) = Matrix.single p q (1 : ℂ) := by
    intro p q
    ext i j
    simp [hΩ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply, ite_and,
      eq_comm, apply_ite (starRingEnd ℂ)]
    split_ifs <;> rfl
  have hamp : ampliation Φ n (Ωᴴ * Ω) =
      (choiMatrix Φ).submatrix (Equiv.prodComm m n) (Equiv.prodComm m n) := by
    ext x y
    simp only [ampliation, choiMatrix, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.prodComm_apply, harg]
    rfl
  have hres := h n (Ωᴴ * Ω) hPSD
  rw [hamp] at hres
  exact (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm m n)).mp hres

/-- **Choi–Jamiołkowski**: a linear map between matrix algebras is completely positive
if and only if its Choi matrix is positive semidefinite. -/
