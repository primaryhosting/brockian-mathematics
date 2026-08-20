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

lemma kraus_of_choi_posSemidef (Φ : MatMap n m) (hC : (choiMatrix Φ).PosSemidef) :
    ∃ V : (Fin n × Fin m) → Matrix (Fin m) (Fin n) ℂ, ∀ A, Φ A = ∑ r, V r * A * (V r)ᴴ := by
  set B := CFC.sqrt (choiMatrix Φ) with hBdef
  have hBp : B.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hB : Bᴴ * B = choiMatrix Φ := by
    rw [hBp.1.eq]
    exact CFC.sqrt_mul_sqrt_self _ hC.nonneg
  refine ⟨fun r => Matrix.of fun s a => star (B r (a, s)), fun A => ?_⟩
  ext s t
  rw [apply_eq_sum_choiMatrix, ← hB]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_star, Finset.mul_sum, Finset.sum_mul]
  have key : ∀ g : Fin n → Fin n → (Fin n × Fin m) → ℂ,
      ∑ a, ∑ b, ∑ r, g a b r = ∑ r, ∑ a, ∑ b, g a b r := fun g =>
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [key (fun a b r => A a b * (star (B r (a, s)) * B r (b, t)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
