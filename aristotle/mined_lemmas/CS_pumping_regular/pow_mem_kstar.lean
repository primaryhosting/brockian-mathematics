/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

variable {α : Type*}

/-- The `n`-fold concatenation of the word `b` with itself. -/

lemma pow_mem_kstar (b : List α) (n : ℕ) : pow b n ∈ KStar.kstar ({b} : Language α) := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n b, rfl, ?_⟩
  intro x hx
  simpa using List.eq_of_mem_replicate hx

/-- **Pumping lemma for regular languages.**
Every regular language `L` admits a pumping length `p > 0`: every word `x ∈ L` with `p ≤ |x|`
can be split as `x = a ++ b ++ c` with `|a| + |b| ≤ p` and `b ≠ []`, such that all pumped words
`a ++ bⁿ ++ c` belong to `L`. -/
