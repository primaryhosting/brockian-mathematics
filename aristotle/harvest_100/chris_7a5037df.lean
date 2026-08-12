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
def nu (H : Finset ℤ) (p : ℕ) : ℕ := (H.image (fun h : ℤ => (h : ZMod p))).card

/-- A finite set of integers is *admissible* if for every prime `p` it misses at least
one residue class modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Admissibility is equivalent to the numerical condition `ν_H(p) < p` for all primes `p`. -/
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
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (nu H p : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- For an admissible tuple, every local factor of the singular series is positive.
(In particular no factor of the singular series vanishes.) -/
theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hnu : nu H p < p := (admissible_iff_nu_lt H).mp hH p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  have h1 : 0 < 1 - (nu H p : ℝ) / p := by
    have : (nu H p : ℝ) < p := by exact_mod_cast hnu
    rw [sub_pos, div_lt_one hppos]
    exact this
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hppos]; linarith
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-- If no prime `p ≤ |H|` divides an element of `H`, then `H` is admissible. -/
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
def primeRange (a b : ℕ) : Finset ℤ :=
  ((Finset.Ioc a b).filter Nat.Prime).image (fun n : ℕ => (n : ℤ))

theorem mem_primeRange {a b : ℕ} {x : ℤ} :
    x ∈ primeRange a b ↔ ∃ q : ℕ, q.Prime ∧ a < q ∧ q ≤ b ∧ x = (q : ℤ) := by
  simp only [primeRange, Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨q, ⟨⟨h1, h2⟩, hq⟩, rfl⟩; exact ⟨q, hq, h1, h2, rfl⟩
  · rintro ⟨q, hq, h1, h2, rfl⟩; exact ⟨q, ⟨⟨h1, h2⟩, hq⟩, rfl⟩

theorem card_primeRange_le (a b : ℕ) : (primeRange a b).card ≤ b - a := by
  refine le_trans Finset.card_image_le ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Nat.card_Ioc]

/-- **New admissible gap ranges.** The primes lying in a window `(a, b]` of width at most
`a` form an admissible tuple. -/
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
theorem SingularSeriesGaps9098 (g : ℕ) (hg : g ≤ 9098) :
    Admissible (primeRange 9098 (9098 + g)) ∧
      (∀ x ∈ primeRange 9098 (9098 + g), ∀ y ∈ primeRange 9098 (9098 + g), |x - y| ≤ (g : ℤ)) ∧
      (∀ p : ℕ, p.Prime → 0 < localFactor (primeRange 9098 (9098 + g)) p) := by
  have hadm : Admissible (primeRange 9098 (9098 + g)) := admissible_primeRange (by omega)
  refine ⟨hadm, ?_, fun p hp => localFactor_pos hadm hp⟩
  intro x hx y hy
  obtain ⟨q, _, hq1, hq2, rfl⟩ := mem_primeRange.mp hx
  obtain ⟨r, _, hr1, hr2, rfl⟩ := mem_primeRange.mp hy
  rw [abs_le]
  omega

/-- The gap ranges of `SingularSeriesGaps9098` are non-vacuous: for `5 ≤ g` the tuple
`primeRange 9098 (9098 + g)` is nonempty (it contains the prime `9103`). -/
theorem primeRange9098_nonempty {g : ℕ} (hg : 5 ≤ g) :
    (primeRange 9098 (9098 + g)).Nonempty :=
  ⟨(9103 : ℤ), mem_primeRange.mpr ⟨9103, by norm_num, by norm_num, by omega, rfl⟩⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

