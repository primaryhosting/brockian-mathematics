/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- `residueCount H p` is the number of distinct residue classes modulo `p`
occupied by the shifts in the tuple `H`. -/
noncomputable def residueCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun h : ℤ => (h : ZMod p))).card

/-- A finite set of integer shifts is *admissible* (in the sense of Hardy–Littlewood)
when, for every prime `p`, it misses at least one residue class modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → residueCount H p < p

/-- The local factor of the Hardy–Littlewood singular series at the prime `p`:
`(1 - ν_H(p)/p) · (1 - 1/p)^(-|H|)`. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (residueCount H p : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- The number of occupied residue classes never exceeds the size of the tuple. -/
theorem residueCount_le_card (H : Finset ℤ) (p : ℕ) : residueCount H p ≤ H.card :=
  Finset.card_image_le

/-- Admissibility is a finite condition: only primes `p ≤ |H|` need to be checked. -/
theorem admissible_of_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → residueCount H p < p) : Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · exact lt_of_le_of_lt (residueCount_le_card H p) (by omega)

/-- Every local factor of an admissible tuple is strictly positive. -/
theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - (residueCount H p : ℝ) / p := by
    have : (residueCount H p : ℝ) < p := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).2 this
    linarith
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]; linarith
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-- The `n`-term *gap ladder*: the shifts `0, n!, 2·n!, …, (n-1)·n!`. -/
noncomputable def gapLadder (n : ℕ) : Finset ℤ :=
  (Finset.range n).image (fun i : ℕ => (i : ℤ) * (n ! : ℤ))

theorem card_gapLadder (n : ℕ) : (gapLadder n).card = n := by
  rw [gapLadder, Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro a b hab
  have hfac : ((n ! : ℤ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have : (a : ℤ) = (b : ℤ) := mul_right_cancel₀ hfac hab
  exact_mod_cast this

/-- For a prime `p ≤ n`, the whole ladder collapses to the single class `0 mod p`. -/
theorem residueCount_gapLadder_small {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ≤ n) :
    residueCount (gapLadder n) p = 1 := by
  have hdvd : p ∣ n ! := Nat.dvd_factorial hp.pos hpn
  have hzero : ((n ! : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  have himg : (gapLadder n).image (fun h : ℤ => (h : ZMod p)) = {0} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    constructor
    · simp only [Finset.mem_image, gapLadder, Finset.mem_image, Finset.mem_range]
      exact ⟨0, ⟨0, hn, by simp⟩, by simp⟩
    · intro x hx
      simp only [Finset.mem_image, gapLadder, Finset.mem_range] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨i, _, rfl⟩ := hy
      push_cast
      rw [hzero, mul_zero]
  rw [residueCount, himg, Finset.card_singleton]

/-- Every gap ladder is admissible. -/
theorem admissible_gapLadder {n : ℕ} (hn : 0 < n) : Admissible (gapLadder n) := by
  intro p hp
  by_cases hpn : p ≤ n
  · rw [residueCount_gapLadder_small hn hp hpn]
    exact lt_of_lt_of_le one_lt_two (by exact_mod_cast hp.two_le)
  · have := residueCount_le_card (gapLadder n) p
    rw [card_gapLadder] at this
    omega

/--
**Singular Series Gaps 9098.**

For every `n ≥ 1` the `n`-element gap range
`{0, n!, 2·n!, …, (n-1)·n!}` is an admissible tuple of shifts: it has exactly `n`
elements, it omits a residue class modulo every prime, and consequently every local
factor of the associated Hardy–Littlewood singular series is strictly positive.
This gives, for each `n`, a new admissible gap range extending the
`SingularSeriesGaps` family.
-/
theorem SingularSeriesGaps9098 (n : ℕ) (hn : 0 < n) :
    (gapLadder n).card = n ∧ Admissible (gapLadder n) ∧
      ∀ p : ℕ, p.Prime → 0 < localFactor (gapLadder n) p :=
  ⟨card_gapLadder n, admissible_gapLadder hn,
    fun _ hp => localFactor_pos (admissible_gapLadder hn) hp⟩

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

