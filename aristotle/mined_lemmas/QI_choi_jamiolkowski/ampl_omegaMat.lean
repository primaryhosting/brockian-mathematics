/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : ℕ}

/-- A linear map between spaces of square complex matrices. -/
abbrev MatMap (n m : ℕ) := Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ

/-- The Choi matrix of a linear map `Φ`:
`C_{(a,s),(b,t)} = Φ(E_{ab})_{s,t}`, i.e. `C = ∑_{a,b} E_{ab} ⊗ Φ(E_{ab})`. -/

lemma ampl_omegaMat (Φ : MatMap n m) : ampl n Φ (omegaMat n) = choiMatrix Φ := by
  ext p q
  simp only [ampl, choiMatrix, Matrix.of_apply]
  have h : (Matrix.of fun i j => omegaMat n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 1 := by
    ext i j
    simp only [omegaMat, Matrix.single_apply, Matrix.of_apply, ite_and, mul_ite, mul_one, mul_zero]
    split_ifs <;> rfl
  rw [h]

/-- The action of `Φ` is determined by its Choi matrix. -/
