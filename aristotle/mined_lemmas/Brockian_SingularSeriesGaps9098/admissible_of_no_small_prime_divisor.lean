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

theorem admissible_of_no_small_prime_divisor {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∀ x ∈ H, ¬ ((p : ℤ) ∣ x)) : Admissible H := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hple : p ≤ H.card
  · refine ⟨0, ?_⟩
    intro x hx
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h p hp hple x hx
  · push_neg at hple
    have hlt : (H.image fun h : ℤ => (h : ZMod p)).card < p :=
      lt_of_le_of_lt Finset.card_image_le hple
    have hne : (H.image fun h : ℤ => (h : ZMod p)) ≠ Finset.univ := by
      intro he
      rw [he, Finset.card_univ, ZMod.card] at hlt
      exact lt_irrefl _ hlt
    by_contra hc
    push_neg at hc
    refine hne (Finset.eq_univ_iff_forall.mpr ?_)
    intro r
    obtain ⟨h', hh', hh'r⟩ := hc r
    exact Finset.mem_image.mpr ⟨h', hh', hh'r⟩

/-- The tuple of primes in the window `(a, b]`, viewed inside `ℤ`. -/
