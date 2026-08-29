import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma adj_apply_split (i j : ZMod 12) :
    adjC12 i j = (if j = i + 1 then (1:ℂ) else 0) + (if j = i - 1 then (1:ℂ) else 0) := by
  have hne : i + 1 ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 12) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  by_cases h1 : j = i + 1
  · subst h1; simp [adjC12, hne]
  · by_cases h2 : j = i - 1
    · subst h2; simp [adjC12, h1]
    · simp [adjC12, h1, h2]

