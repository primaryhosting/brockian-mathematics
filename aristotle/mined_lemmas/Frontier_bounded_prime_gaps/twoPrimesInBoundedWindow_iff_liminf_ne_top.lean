import Mathlib
/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, the gap between the `n`-th and `(n+1)`-st prime
(with `p_0 = 2`, i.e. `p_n = Nat.nth Nat.Prime n`). -/

theorem twoPrimesInBoundedWindow_iff_liminf_ne_top :
    TwoPrimesInBoundedWindow ↔ liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := frequently_gap_le h
    have hle : liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
      liminf_le_of_frequently_le (hB.mono fun n hn => by exact_mod_cast hn)
    intro htop
    rw [htop] at hle
    simp at hle
  · intro h
    obtain ⟨L, hL⟩ : ∃ L : ℕ, liminf (fun n => (primeGap n : ℕ∞)) atTop < (L : ℕ∞) := by
      obtain ⟨L, hLeq⟩ := ENat.ne_top_iff_exists.1 h
      refine ⟨L + 1, ?_⟩
      rw [← hLeq]
      exact_mod_cast Nat.lt_succ_self L
    have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) < (L : ℕ∞) :=
      frequently_lt_of_liminf_lt (h := hL)
    refine ⟨L, fun N => ?_⟩
    rw [frequently_atTop] at hfreq
    obtain ⟨n, hn, hgap⟩ := hfreq N
    have hgap' : primeGap n < L := by exact_mod_cast hgap
    refine ⟨Nat.nth Nat.Prime n, Nat.nth Nat.Prime (n + 1), Nat.prime_nth_prime n,
      Nat.prime_nth_prime (n + 1), ?_, ?_, ?_⟩
    · exact le_trans hn (Nat.le_nth fun hf => absurd hf primes_infinite)
    · exact (Nat.nth_lt_nth primes_infinite).2 (Nat.lt_succ_self n)
    · have hmono : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1) :=
        ((Nat.nth_lt_nth primes_infinite).2 (Nat.lt_succ_self n)).le
      have : primeGap n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n := rfl
      omega

/-! ### Base cases and a further reduction -/

