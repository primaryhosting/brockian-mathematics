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

theorem admissible_iff_nu_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu H p < p := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : H.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr ?_
      intro he
      have : r ∈ H.image (fun h : ℤ => (h : ZMod p)) := by rw [he]; exact Finset.mem_univ r
      obtain ⟨h, hh, hhr⟩ := Finset.mem_image.mp this
      exact hr h hh hhr
    have := Finset.card_lt_card hsub
    simpa [nu, Finset.card_univ, ZMod.card] using this
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have h := hH p hp
    by_contra hc
    push_neg at hc
    have : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr ?_
      intro r
      obtain ⟨h', hh', hh'r⟩ := hc r
      exact Finset.mem_image.mpr ⟨h', hh', hh'r⟩
    rw [nu, this, Finset.card_univ, ZMod.card] at h
    exact lt_irrefl _ h

/-- The local factor at `p` of the Hardy–Littlewood singular series of the tuple `H`. -/
