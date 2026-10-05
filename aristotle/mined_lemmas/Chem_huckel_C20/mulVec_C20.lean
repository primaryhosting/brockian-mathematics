import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma mulVec_C20 (x : ZMod 20 → ℂ) (i : ZMod 20) :
    (C20 *ᵥ x) i = x (i - 1) + x (i + 1) := by
  have hne : (i - 1 : ZMod 20) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination -h
    revert h2; decide
  have hiff : ∀ j : ZMod 20, (i - j = 1 ∨ j - i = 1) ↔ (j = i - 1 ∨ j = i + 1) := by
    intro j
    constructor
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
  have hstep : ∀ j : ZMod 20,
      C20 i j * x j = if j ∈ ({i - 1, i + 1} : Finset (ZMod 20)) then x j else 0 := by
    intro j
    simp only [C20_apply, hiff j, Finset.mem_insert, Finset.mem_singleton, ite_mul, one_mul,
      zero_mul]
  rw [Matrix.mulVec, dotProduct]
  simp only [hstep]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]

