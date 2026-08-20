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

theorem amplify_maxEnt (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    amplify Φ n (maxEnt n) = choiMatrix Φ := by
  ext x y
  have h : (Matrix.of fun i j => maxEnt n (x.1, i) (y.1, j)) = Matrix.single x.1 y.1 (1 : ℂ) := by
    ext i j
    simp [maxEnt, Matrix.single_apply, eq_comm]
  simp [amplify, choiMatrix, h]

omit [Fintype m] [DecidableEq m] in
