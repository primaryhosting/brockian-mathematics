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

theorem twoPrimesInBoundedWindow_of_DHL2 (h : DHL2) : TwoPrimesInBoundedWindow := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.sup id, fun N => ?_⟩
  obtain ⟨n, hn, hcard⟩ := hH N
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_filter] at ha hb
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨n + a, n + b, ha.2, hb.2, le_add_right hn, by omega,
      by have := Finset.le_sup (f := id) hb.1; simp at this; omega⟩
  · exact ⟨n + b, n + a, hb.2, ha.2, le_add_right hn, by omega,
      by have := Finset.le_sup (f := id) ha.1; simp at this; omega⟩

/-- From two primes in a bounded window, arbitrarily far out, we get a uniform bound on
infinitely many *consecutive* prime gaps. -/
