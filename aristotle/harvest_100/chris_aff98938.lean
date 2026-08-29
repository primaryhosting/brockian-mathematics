/-
/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
(Lean requires the `import` command to be the very first command of a file, so
the header above is reproduced verbatim inside this comment and again as the
module docstring below.)
-/
import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- The set of residue classes modulo `p` that are occupied by the shift set `H`. -/
def coveredResidues (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℤ => (h : ZMod p))

/-- A finite set of integer shifts (a "gap pattern") is *admissible* if for every prime `p`
it misses at least one residue class modulo `p`.  This is exactly the condition under which
the Hardy–Littlewood singular series of the tuple is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Missing a residue class mod `p` is the same as covering fewer than `p` classes. -/
theorem exists_missed_residue_iff_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime) :
    (∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ↔ (coveredResidues H p).card < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  constructor
  · rintro ⟨r, hr⟩
    have hrn : r ∉ coveredResidues H p := by
      simp only [coveredResidues, Finset.mem_image, not_exists]
      rintro h ⟨hh, rfl⟩
      exact hr h hh rfl
    calc (coveredResidues H p).card < Finset.univ.card := by
            refine Finset.card_lt_card ?_
            refine Finset.ssubset_univ_iff.mpr ?_
            intro hcontra
            exact hrn (hcontra ▸ Finset.mem_univ r)
      _ = p := by simp [Finset.card_univ, hcard]
  · intro hlt
    by_contra hcon
    push_neg at hcon
    have huniv : coveredResidues H p = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr ?_
      intro r
      obtain ⟨h, hh, hhr⟩ := hcon r
      simp only [coveredResidues, Finset.mem_image]
      exact ⟨h, hh, by simpa using hhr⟩
    rw [huniv] at hlt
    simp [Finset.card_univ, hcard] at hlt

/-- Pigeonhole: a set of `k` shifts can only occupy `k` residue classes, so all primes
exceeding the size of the pattern are automatically harmless.  This is the reformulation
that reduces admissibility to a *finite* check. -/
theorem admissible_iff_small_primes (H : Finset ℤ) :
    Admissible H ↔
      ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    by_cases hle : p ≤ H.card
    · exact hH p hp hle
    · push_neg at hle
      refine (exists_missed_residue_iff_card_lt hp).mpr ?_
      exact lt_of_le_of_lt (Finset.card_image_le) hle

/-- A pattern all of whose shifts avoid divisibility by every prime up to its own size
is admissible: for such primes the class `0` is missed, and larger primes are handled by
pigeonhole. -/
theorem admissible_of_not_dvd_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∀ x ∈ H, ¬ ((p : ℤ) ∣ x)) :
    Admissible H := by
  refine (admissible_iff_small_primes H).mpr ?_
  intro p hp hple
  refine ⟨0, ?_⟩
  intro x hx hx0
  exact h p hp hple x hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx0)

/-- **Main result (admissible gap ranges).**
Let `k` be a length, `a` a starting point and `d` a common difference such that every prime
`p ≤ k` divides `d` but does not divide `a`.  Then the arithmetic progression
`a, a + d, …, a + (k-1)d` is an admissible pattern of shifts: modulo every prime it misses a
residue class, hence its Hardy–Littlewood singular series does not vanish.

This produces admissible gap ranges of arbitrary length `k` and arbitrary diameter `(k-1)|d|`,
extending the `SingularSeriesGaps` family. -/
theorem SingularSeriesGaps13501360 (k : ℕ) (a d : ℤ)
    (hd : ∀ p : ℕ, p.Prime → p ≤ k → ((p : ℤ) ∣ d))
    (ha : ∀ p : ℕ, p.Prime → p ≤ k → ¬ ((p : ℤ) ∣ a)) :
    Admissible ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * d)) := by
  refine admissible_of_not_dvd_small_primes ?_
  intro p hp hple x hx hdvd
  have hcard : ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * d)).card ≤ k := by
    simpa using (Finset.card_image_le (s := Finset.range k) (f := fun i : ℕ => a + (i : ℤ) * d))
  have hpk : p ≤ k := le_trans hple hcard
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hdd : (p : ℤ) ∣ (i : ℤ) * d := Dvd.dvd.mul_left (hd p hp hpk) _
  have hsub : (p : ℤ) ∣ (a + (i : ℤ) * d) - (i : ℤ) * d := dvd_sub hdvd hdd
  simp only [add_sub_cancel_right] at hsub
  exact ha p hp hpk hsub

/-- The primorial-type difference: the product of all primes up to `k`. -/
def smallPrimeProduct (k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p

/-- Concrete instance of the main theorem: for every `k`, the arithmetic progression of
length `k` starting at `1` with common difference the product of all primes `≤ k` is an
admissible pattern. -/
theorem admissible_one_add_smallPrimeProduct (k : ℕ) :
    Admissible ((Finset.range k).image (fun i : ℕ => 1 + (i : ℤ) * (smallPrimeProduct k : ℤ))) := by
  refine SingularSeriesGaps13501360 k 1 (smallPrimeProduct k : ℤ) ?_ ?_
  · intro p hp hpk
    have : p ∣ smallPrimeProduct k := by
      refine Finset.dvd_prod_of_mem _ ?_
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    exact_mod_cast Int.natCast_dvd_natCast.mpr this
  · intro p hp _ hdvd
    have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega

/-- The local factor of the Hardy–Littlewood singular series at the prime `p`:
`(1 - ν_H(p)/p) / (1 - 1/p)^{|H|}` where `ν_H(p)` is the number of occupied residue classes. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (coveredResidues H p).card / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ H.card

/-- For an admissible pattern every local factor of the singular series is strictly positive
(so no factor of the singular series vanishes). -/
theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt : ((coveredResidues H p).card : ℝ) < (p : ℝ) := by
    exact_mod_cast (exists_missed_residue_iff_card_lt hp).mp (hH p hp)
  have hnum : 0 < 1 - ((coveredResidues H p).card : ℝ) / (p : ℝ) := by
    have : ((coveredResidues H p).card : ℝ) / (p : ℝ) < 1 := (div_lt_one hppos).mpr hlt
    linarith
  have hden : 0 < (1 - 1 / (p : ℝ)) ^ H.card := by
    refine pow_pos ?_ _
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    linarith
  exact div_pos hnum hden

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

