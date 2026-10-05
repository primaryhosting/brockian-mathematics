import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma C9adj_apply (i j : ZMod 9) :
    C9adj i j = (if j = i + 1 then 1 else 0) + (if j = i - 1 then (1 : ℂ) else 0) := by
  have hne : (i + 1 : ZMod 9) ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 9) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
    simp [C9adj, h1, h2] at * <;> tauto

