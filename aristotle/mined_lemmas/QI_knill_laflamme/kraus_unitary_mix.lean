/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/

theorem kraus_unitary_mix (E : Fin m → Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U * Uᴴ = 1) :
    ∑ k, (∑ a, U a k • E a) * ρ * (∑ a, U a k • E a)ᴴ = ∑ a, E a * ρ * (E a)ᴴ := by
  have step : ∀ k : Fin m, (∑ a, U a k • E a) * ρ * (∑ a, U a k • E a)ᴴ
      = ∑ a, ∑ b, (U a k * (starRingEnd ℂ) (U b k)) • (E a * ρ * (E b)ᴴ) := by
    intro k
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
      Finset.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  simp only [step]
  rw [Finset.sum_comm]
  have key : ∀ a : Fin m, ∑ k, ∑ b, (U a k * (starRingEnd ℂ) (U b k)) • (E a * ρ * (E b)ᴴ)
      = ∑ b, ((U * Uᴴ) a b) • (E a * ρ * (E b)ᴴ) := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_smul]; congr 1
  simp only [key, hU, Matrix.one_apply]
  exact Finset.sum_congr rfl fun a _ => by simp

/-- The mixed error operators satisfy diagonal Knill–Laflamme relations. -/
