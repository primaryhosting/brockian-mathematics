/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/

theorem mul_krausAmp_conjTranspose_apply {κ : Type} [Fintype κ] [DecidableEq κ]
    (K : Matrix m n ℂ) (Y : Matrix (κ × m) (κ × n) ℂ) (x y : κ × m) :
    (Y * (krausAmp κ K)ᴴ) x y = ∑ j, Y x (y.1, j) * star (K y.2 j) := by
  simp only [Matrix.mul_apply, krausAmp, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, apply_ite star, star_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- A Kraus representation of `Φ` amplifies to a Kraus representation of `id_κ ⊗ Φ`. -/
