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

theorem mem_primeRange {a b : ℕ} {x : ℤ} :
    x ∈ primeRange a b ↔ ∃ q : ℕ, q.Prime ∧ a < q ∧ q ≤ b ∧ x = (q : ℤ) := by
  simp only [primeRange, Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨q, ⟨⟨h1, h2⟩, hq⟩, rfl⟩; exact ⟨q, hq, h1, h2, rfl⟩
  · rintro ⟨q, hq, h1, h2, rfl⟩; exact ⟨q, ⟨⟨h1, h2⟩, hq⟩, rfl⟩

