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

theorem quad_form (P M : Matrix (Fin n) (Fin n) ℂ) (hherm : Pᴴ = P) (ψ : Fin n → ℂ)
    (hψ : P *ᵥ ψ = ψ) :
    star ψ ⬝ᵥ ((P * Mᴴ * M * P) *ᵥ ψ) = star (M *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ) := by
  have e : (P * Mᴴ * M * P) *ᵥ ψ = P *ᵥ (Mᴴ *ᵥ (M *ᵥ (P *ᵥ ψ))) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hψ, dot_mulVec_adj P ψ, hherm, hψ, dot_mulVec_adj Mᴴ ψ,
    Matrix.conjTranspose_conjTranspose]

