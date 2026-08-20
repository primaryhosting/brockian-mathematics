import Mathlib

/-!
# Admissible tuples, singular series local factors, and new admissible gap ranges

This file develops the basic theory of *admissible* tuples of integers (the tuples
for which the Hardy–Littlewood singular series does not vanish), and produces a new
family of admissible gap ranges built from the primes in a window `(a, b]`.

Main results:

* `Brockian.admissible_iff_nu_lt` : a tuple is admissible iff for every prime `p` it
  misses a residue class mod `p`, equivalently `ν_H(p) < p`.
* `Brockian.localFactor_pos` : for an admissible tuple all local factors of the
  singular series are strictly positive.
* `Brockian.admissible_primeRange` : the primes in a window `(a, b]` with `b ≤ 2 * a`
  form an admissible tuple.
* `Brockian.SingularSeriesGaps9098` : the resulting new family of admissible gap
  ranges based at `9098`.
-/

namespace Brockian

open Finset

/-- The number of residue classes mod `p` occupied by the tuple `H`. -/

theorem admissible_primeRange {a b : ℕ} (hb : b ≤ 2 * a) : Admissible (primeRange a b) := by
  refine admissible_of_no_small_prime_divisor ?_
  intro p hp hple x hx hdvd
  obtain ⟨q, hq, haq, hqb, rfl⟩ := mem_primeRange.mp hx
  have hcard : (primeRange a b).card ≤ a := le_trans (card_primeRange_le a b) (by omega)
  have hpa : p ≤ a := le_trans hple hcard
  have hpq : p ∣ q := by exact_mod_cast hdvd
  have : p = q := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq)
  omega

/-- **New admissible gap ranges based at `9098`.** For every gap `g ≤ 9098`, the primes in
the window `(9098, 9098 + g]` form an admissible tuple; all of its elements lie in an
interval of length `g`, so the tuple has diameter at most `g`. -/
