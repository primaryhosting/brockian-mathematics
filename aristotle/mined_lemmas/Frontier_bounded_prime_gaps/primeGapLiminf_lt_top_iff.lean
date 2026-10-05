import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` to precede all commands, including this module docstring,
so the header comment appears immediately after the single `import Mathlib` line.)

## Contents

We formalize the statement "the liminf of the sequence of prime gaps `p_{n+1} - p_n` is finite"
(the Zhang / Maynard theorem) as `Frontier.primeGapLiminf < ⊤`, where the liminf is taken in
`ℕ∞ = WithTop ℕ`, and we give a Lean-checked reduction: this liminf is finite **iff** there is a
constant `B` such that arbitrarily far out one can find two primes `p < q` with `q - p ≤ B`.

The reduction is proved unconditionally; it turns the analytic statement about the liminf of the
gap sequence into the purely combinatorial statement that is the actual content of the
Zhang / Maynard theorem (which is not proved here).
-/

open Filter

namespace Frontier

/-- The `n`-th prime number, `p n`, with `p 0 = 2`. -/

lemma primeGapLiminf_lt_top_iff :
    primeGapLiminf < ⊤ ↔ ∃ B : ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ primeGap n ≤ B := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.mp h.ne
    refine ⟨B, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨N, hN⟩ := hcon
    have hev : ∀ᶠ n in atTop, ((B : ℕ∞) + 1) ≤ (primeGap n : ℕ∞) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 : (B : ℕ) + 1 ≤ primeGap n := hN n hn
      exact_mod_cast h1
    have h2 : ((B : ℕ∞) + 1) ≤ primeGapLiminf :=
      le_liminf_of_le (u := fun n => (primeGap n : ℕ∞)) (f := atTop) ⟨⊤, by simp⟩ hev
    rw [← hB] at h2
    have h3 : ((B + 1 : ℕ) : ℕ∞) ≤ ((B : ℕ) : ℕ∞) := by push_cast; exact h2
    have h4 : B + 1 ≤ B := Nat.cast_le (α := ℕ∞) |>.mp h3
    omega
  · rintro ⟨B, hB⟩
    have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) ≤ (B : ℕ∞) := by
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn, hle⟩ := hB N
      exact ⟨n, hn, by exact_mod_cast hle⟩
    exact lt_of_le_of_lt (Filter.liminf_le_of_frequently_le hfreq) (by simp)

/-- A pair of primes `p < q` with `q ≤ p + B` yields a gap between *consecutive* primes
of size at most `B`, namely at the index of `p`. -/
