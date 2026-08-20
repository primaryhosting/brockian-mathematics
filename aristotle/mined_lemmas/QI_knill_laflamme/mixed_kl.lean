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

theorem mixed_kl (P : Matrix (Fin n) (Fin n) ℂ) (E : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (c : Matrix (Fin m) (Fin m) ℂ) (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P)
    (U : Matrix (Fin m) (Fin m) ℂ) (k l : Fin m) :
    P * (∑ a, U a k • E a)ᴴ * (∑ b, U b l • E b) * P = ((Uᴴ * c * U) k l) • P := by
  have expand : P * (∑ a, U a k • E a)ᴴ * (∑ b, U b l • E b) * P
      = ∑ a, ∑ b, ((starRingEnd ℂ) (U a k) * U b l) • (P * (E a)ᴴ * E b * P) := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
      Finset.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  rw [expand]
  simp only [hc, smul_smul, ← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ## The Knill–Laflamme conditions imply correctability -/

