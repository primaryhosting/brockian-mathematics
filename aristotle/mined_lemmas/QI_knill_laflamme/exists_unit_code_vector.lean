/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem exists_unit_code_vector {P : Matrix n n ℂ} (hP : IsProj P) (hP0 : P ≠ 0) :
    ∃ u : n → ℂ, P *ᵥ u = u ∧ ip u u = 1 := by
  have hx : ∃ x : n → ℂ, P *ᵥ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hP0 ?_
    ext p q
    have := congrFun (hcon (Pi.single q 1)) p
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  obtain ⟨x, hxne⟩ := hx
  obtain ⟨r, hr, hru⟩ := exists_unit_smul hxne
  exact ⟨r • (P *ᵥ x), by rw [mulVec_smul, mulVec_mulVec, hP.idem], hru⟩

