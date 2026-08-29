/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Language Computability

/-- `pump y i` is the concatenation of `i` copies of the word `y`. -/

lemma pump_mem_kstar {α : Type*} (y : List α) (i : ℕ) : pump y i ∈ ({y} : Language α)∗ := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate i y, rfl, ?_⟩
  intro z hz
  simpa using List.eq_of_mem_replicate hz

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0`: every word `w ∈ L` of length at
least `p` can be split as `w = x ++ y ++ z` with `|x ++ y| ≤ p` and `y ≠ []`, in such a way
that `x ++ yⁱ ++ z ∈ L` for every `i : ℕ`.

The core combinatorial content is Mathlib's `DFA.pumping_lemma`.
-/
