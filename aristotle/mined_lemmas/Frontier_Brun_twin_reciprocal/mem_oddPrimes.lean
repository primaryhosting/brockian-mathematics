import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma mem_oddPrimes {z p : ℕ} : p ∈ oddPrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddPrimes, Nat.lt_succ_iff, and_assoc]

