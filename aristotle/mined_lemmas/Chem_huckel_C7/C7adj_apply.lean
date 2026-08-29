/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem C7adj_apply (i j : ZMod 7) :
    C7adj i j = (if j = i - 1 then (1 : ℂ) else 0) + (if j = i + 1 then 1 else 0) := by
  have e1 : (i - j = 1) ↔ j = i - 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  have e2 : (j - i = 1) ↔ j = i + 1 :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have hne : (i - 1 : ZMod 7) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 7) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  simp only [C7adj, Matrix.of_apply, e1, e2]
  by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;> simp [h1, h2] at * <;> simp_all

/-- The action of the adjacency matrix on a vector: the neighbours of `i` are `i-1` and `i+1`. -/
