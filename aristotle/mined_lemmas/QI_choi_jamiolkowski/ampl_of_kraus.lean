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

lemma ampl_of_kraus {ι : Type} [Fintype ι] (Φ : MatMap n m)
    (V : ι → Matrix (Fin m) (Fin n) ℂ) (hΦ : ∀ A, Φ A = ∑ r, V r * A * (V r)ᴴ)
    (k : ℕ) (X : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    ampl k Φ X = ∑ r, kronId k (V r) * X * (kronId k (V r))ᴴ := by
  ext p q
  obtain ⟨a, s⟩ := p
  obtain ⟨b, t⟩ := q
  simp only [ampl, Matrix.of_apply, hΦ, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, kronId, Fintype.sum_prod_type, ite_mul, zero_mul, apply_ite,
    mul_zero, star_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-- Choi's theorem, hard direction: a positive semidefinite Choi matrix yields a Kraus
representation of `Φ`. -/
