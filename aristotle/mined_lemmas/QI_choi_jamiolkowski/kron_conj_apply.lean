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

private lemma kron_conj_apply {d : Type} [Fintype d] [DecidableEq d]
    (V : Matrix m n ℂ) (A : Matrix (n × d) (n × d) ℂ) (x y : m × d) :
    ((Matrix.of fun (u : m × d) (v : n × d) => V u.1 v.1 * (if u.2 = v.2 then 1 else 0)) * A *
      (Matrix.of fun (u : m × d) (v : n × d) => V u.1 v.1 * (if u.2 = v.2 then 1 else 0))ᴴ) x y
      = ∑ i, ∑ j, V x.1 i * A (i, x.2) (j, y.2) * (starRingEnd ℂ) (V y.1 j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq, mul_comm, mul_assoc]
  simp only [Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Entrywise description of the conjugation `W X Wᴴ`. -/
