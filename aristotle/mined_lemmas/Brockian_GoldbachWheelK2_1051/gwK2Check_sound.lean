/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality, stated in the usual way: `p` is at least `2` and its only divisors are
`1` and `p`. (This file is self-contained, so the predicate is spelled out here.) -/

theorem gwK2Check_sound {n : Nat} (hn : n ≤ 1051) (h : gwK2Check n = true) :
    ∃ p q : Nat, GwPrime p ∧ GwPrime q ∧ p + q = n := by
  rw [gwK2Check, List.any_eq_true] at h
  obtain ⟨p, _, hp⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hp1, hple⟩, hp3⟩ := hp
  exact ⟨p, n - p, gwIsPrime_sound (by omega) hp1, gwIsPrime_sound (by omega) hp3, by omega⟩

/-- The wheel test succeeds for every even `n` with `4 ≤ n ≤ 1051`. -/
