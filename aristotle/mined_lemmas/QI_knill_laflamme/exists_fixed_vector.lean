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

theorem exists_fixed_vector {P : Matrix (Fin n) (Fin n) ℂ} (hidem : P * P = P) (hP0 : P ≠ 0) :
    ∃ ψ : Fin n → ℂ, P *ᵥ ψ = ψ ∧ ψ ≠ 0 := by
  have hex : ∃ v : Fin n → ℂ, P *ᵥ v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hP0 ?_
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  obtain ⟨v, hv⟩ := hex
  exact ⟨P *ᵥ v, by rw [Matrix.mulVec_mulVec, hidem], hv⟩

/-- Conjugating a sum of Kraus terms. -/
