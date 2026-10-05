import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma A_apply (i j : ZMod 15) :
    A i j = (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  have h1 : (i - j = 1) ↔ j = i - 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  have h2 : (j - i = 1) ↔ j = i + 1 :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have hne : ¬ (j = i - 1 ∧ j = i + 1) := by
    rintro ⟨rfl, h⟩
    have h2 : (2 : ZMod 15) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  unfold A
  simp only [h1, h2]
  by_cases ha : j = i - 1 <;> by_cases hb : j = i + 1 <;> simp_all

/-- Matrix-vector product with the adjacency matrix is the "neighbour sum". -/
