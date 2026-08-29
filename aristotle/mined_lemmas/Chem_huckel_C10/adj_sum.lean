import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
`i` and `j` are adjacent iff they differ by `1` modulo `10`. -/

lemma adj_sum {R : Type*} [CommRing R] (f : ZMod 10 → R) (i : ZMod 10) :
    ∑ j : ZMod 10, (if i - j = 1 ∨ j - i = 1 then (1 : R) else 0) * f j
      = f (i - 1) + f (i + 1) := by
  have hne : ∀ a : ZMod 10, a - 1 ≠ a + 1 := by decide
  have hiff : ∀ a b : ZMod 10, (a - b = 1 ∨ b - a = 1) ↔ (b = a - 1 ∨ b = a + 1) := by decide
  have key : ∀ j : ZMod 10,
      (if i - j = 1 ∨ j - i = 1 then (1 : R) else 0) * f j
        = (if j = i - 1 then f j else 0) + (if j = i + 1 then f j else 0) := by
    intro j
    rw [if_congr (hiff i j) rfl rfl]
    by_cases h1 : j = i - 1
    · subst h1
      simp [hne i]
    · by_cases h2 : j = i + 1
      · subst h2
        simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  simp

