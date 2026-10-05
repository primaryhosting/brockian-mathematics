/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma C14adj_apply (i j : ZMod 14) :
    C14adj i j = (if j = i + 1 then (1 : ℂ) else 0) + (if j = i - 1 then 1 else 0) := by
  have hne : (i + 1 : ZMod 14) ≠ i - 1 := by
    intro h
    have : (1 : ZMod 14) = -1 := by linear_combination h
    exact absurd this (by decide)
  unfold C14adj
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;> simp [h1, h2] at * <;> tauto

