/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean 4
does not allow a module docstring to precede the `import` commands.)
-/

open Filter

namespace Frontier

/-- The `n`-th prime number (`nthPrime 0 = 2`). -/

lemma liminf_lt_top_iff (f : ℕ → ℕ) :
    liminf (fun n => (f n : ℕ∞)) atTop < ⊤ ↔ ∃ B : ℕ, ∃ᶠ n in atTop, f n ≤ B := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.1 h.ne
    refine ⟨L, ?_⟩
    by_contra hcon
    rw [not_frequently] at hcon
    have hev : ∀ᶠ n in atTop, ((L : ℕ∞) + 1) ≤ (f n : ℕ∞) := by
      filter_upwards [hcon] with n hn
      have : L + 1 ≤ f n := by omega
      exact_mod_cast this
    have : ((L : ℕ∞) + 1) ≤ liminf (fun n => (f n : ℕ∞)) atTop := by
      rw [liminf_eq]
      exact le_sSup hev
    rw [← hL] at this
    have hfin : L + 1 ≤ L := by exact_mod_cast this
    omega
  · rintro ⟨B, hB⟩
    refine lt_of_le_of_lt (liminf_le_of_frequently_le' (x := (B : ℕ∞)) ?_) ?_
    · exact hB.mono fun n hn => by exact_mod_cast hn
    · exact WithTop.coe_lt_top B

/--
**Bounded prime gaps** (Zhang–Maynard), stated as a Lean-checked reduction.

The assertion that the liminf of the prime gaps `p_{n+1} - p_n` is finite is *equivalent*
to the assertion proved by Zhang and Maynard: there is a bound `B` such that arbitrarily
large pairs of primes `p < q` satisfy `q ≤ p + B`.
-/
