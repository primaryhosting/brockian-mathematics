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

theorem apply_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ)
    (a b : m) : Φ X a b = ∑ i, ∑ j, X i j * choiMatrix Φ (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    ext a' b'; simp [Matrix.single_apply]
  rw [h, map_smul]
  simp [choiMatrix]

omit [DecidableEq m] in
/-- A positive semidefinite Choi matrix yields a Kraus representation, obtained by
factoring `C = Bᴴ B`. -/
