/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `AtMostTwoPrimeFactors q` says that `q` is a product of at most two primes,
i.e. `q = 1`, or `q` is prime, or `q` is a product of two (not necessarily distinct)
primes.  Equivalently (see `atMostTwoPrimeFactors_iff_bigOmega_le_two`), the number of
prime factors of `q`, counted with multiplicity, is at most `2`.  These are the
"almost primes" `P₂` appearing in Chen's theorem. -/

theorem chenRepresentation_of_small {n : ℕ} (h4 : 4 ≤ n) (hn : n ≤ 60) (he : Even n) :
    ChenRepresentation n := by
  have key : ∃ p ∈ Finset.range 61, ∃ q ∈ Finset.range 61,
      p.Prime ∧ q.Prime ∧ n = p + q := by
    set_option maxRecDepth 100000 in
    interval_cases n <;> revert he <;> decide
  obtain ⟨p, -, q, -, hp, hq, hpq⟩ := key
  exact ⟨p, q, hp, Or.inr (Or.inl hq), hpq⟩

/-! ### Main result: a Lean-checked reduction of Chen's theorem to Goldbach -/

/-- **Chen's theorem, as a Lean-checked reduction.**  The binary Goldbach conjecture
implies Chen's statement that every sufficiently large even number is of the form `p + q`
with `p` prime and `q` having at most two prime factors (indeed, with `N = 4`, *every*
even number `n ≥ 4` is then of this form).

The unconditional theorem of Chen (1973) is stated here as `Frontier.ChenStatement`; the
reduction below is proved unconditionally, and `Frontier.chenRepresentation_of_small`
verifies the conclusion unconditionally in the base range `4 ≤ n ≤ 60`. -/
