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

theorem krausAmp_mul_apply {κ : Type} [Fintype κ] [DecidableEq κ] (K : Matrix m n ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) (x : κ × m) (w : κ × n) :
    (krausAmp κ K * X) x w = ∑ i, K x.2 i * X (x.1, i) w := by
  simp only [Matrix.mul_apply, krausAmp, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
