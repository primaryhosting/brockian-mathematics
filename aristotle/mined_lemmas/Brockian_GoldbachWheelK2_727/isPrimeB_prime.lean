/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000000

namespace Brockian

/-- `trialDivB n f d` performs trial division of `n` by the successive divisors
`d, d+1, ...` (using at most `f` steps), stopping successfully as soon as the
divisor exceeds `√n`. It returns `true` only when no divisor `≥ d` with
`k * k ≤ n` divides `n`. -/

theorem isPrimeB_prime {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB] at h
  by_cases h2 : n = 2
  · subst h2; exact Nat.prime_two
  · simp only [beq_iff_eq, h2, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn2, hloop⟩ := h
    refine Nat.prime_def_le_sqrt.mpr ⟨hn2, fun m hm hms => ?_⟩
    exact trialDivB_sound n n 2 hloop m hm (Nat.le_sqrt.mp hms)

/-- **Key intermediate lemma (the wheel check).**
Every even `n` with `4 ≤ n ≤ 2 * 727` has a summand `p < 100` such that both
`p` and `n - p` pass the Boolean primality test. -/
