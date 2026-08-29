/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Key Mathlib ingredients used: `Finset.card_image_le` (a tuple occupies at most `#H`
residue classes, so only primes `p ≤ #H` can obstruct admissibility),
`ZMod.intCast_zmod_eq_zero_iff_dvd` and `even_iff_two_dvd` (the prime `2` analysis),
`Finset.prod_pos` and `zpow_pos` (positivity of the singular series).
-/

open Finset

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the integer tuple `H`. -/
def residues (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℤ => (h : ZMod p))

/-- A finite tuple of integers is *admissible* if for every prime `p` it fails to
cover all residue classes modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (residues H p).card < p

/-- The local factor of the Hardy–Littlewood singular series at the prime `p`. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (residues H p).card / p) * (1 - 1 / p) ^ (-(H.card : ℤ))

/-- The partial singular series: the product of the local factors over the primes `< N`. -/
noncomputable def partialSingularSeries (H : Finset ℤ) (N : ℕ) : ℝ :=
  ∏ p ∈ (range N).filter Nat.Prime, localFactor H p

/-- The number of occupied residue classes never exceeds the size of the tuple. -/
lemma card_residues_le (H : Finset ℤ) (p : ℕ) : (residues H p).card ≤ H.card :=
  Finset.card_image_le

/-- Large primes never obstruct admissibility. -/
lemma residues_card_lt_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : H.card < p) :
    (residues H p).card < p :=
  lt_of_le_of_lt (card_residues_le H p) hp

/-- Admissibility only has to be checked at the primes `p ≤ H.card`. -/
lemma admissible_iff_small_primes (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → (residues H p).card < p := by
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    rcases le_or_gt p H.card with hle | hgt
    · exact h p hp hle
    · exact residues_card_lt_of_card_lt hgt

/-- The residues of a pair `{0, d}` modulo `p`. -/
lemma residues_pair (d : ℤ) (p : ℕ) :
    residues ({0, d} : Finset ℤ) p = {0, (d : ZMod p)} := by
  classical
  by_cases h : (0 : ℤ) = d
  · subst h
    simp [residues]
  · simp [residues]

/-- **Admissible gaps.** The pair `{0, d}` is admissible exactly when `d` is even. -/
theorem pair_admissible_iff_even (d : ℤ) :
    Admissible ({0, d} : Finset ℤ) ↔ Even d := by
  classical
  constructor
  · intro h
    have h2 := h 2 Nat.prime_two
    rw [residues_pair] at h2
    have hd : (d : ZMod 2) = 0 := by
      by_contra hne
      have : ({0, (d : ZMod 2)} : Finset (ZMod 2)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using hne), Finset.card_singleton]
      omega
    have : (2 : ℤ) ∣ d := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).1 hd
    exact (even_iff_two_dvd).2 this
  · intro hd p hp
    rcases eq_or_ne p 2 with rfl | hne
    · rw [residues_pair]
      have hd0 : (d : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).2 (by exact_mod_cast (even_iff_two_dvd).1 hd)
      rw [hd0]
      simp
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hcard : (({0, d} : Finset ℤ)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact lt_of_le_of_lt (le_trans (card_residues_le _ _) hcard) (by omega)

/-- Each local factor of an admissible tuple is strictly positive. -/
theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - ((residues H p).card : ℝ) / (p : ℝ) := by
    have hlt : ((residues H p).card : ℝ) < (p : ℝ) := by exact_mod_cast hH p hp
    have : ((residues H p).card : ℝ) / (p : ℝ) < 1 := (div_lt_one hp0).2 hlt
    linarith
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-- The partial singular series of an admissible tuple is strictly positive. -/
theorem partialSingularSeries_pos {H : Finset ℤ} (hH : Admissible H) (N : ℕ) :
    0 < partialSingularSeries H N := by
  refine Finset.prod_pos ?_
  intro p hp
  exact localFactor_pos hH (Finset.mem_filter.1 hp).2

/-- **Singular Series Gaps 12401250.**

Within the gap range `1240 ≤ d ≤ 1250`, the admissible gaps `d` — i.e. those for which the
pair `{0, d}` is an admissible tuple — are exactly the even ones, namely
`1240, 1242, 1244, 1246, 1248, 1250`; and for each of these gaps every partial
Hardy–Littlewood singular series of the corresponding pair is strictly positive. -/
theorem SingularSeriesGaps12401250 :
    {d : ℤ | 1240 ≤ d ∧ d ≤ 1250 ∧ Admissible ({0, d} : Finset ℤ)}
        = ({1240, 1242, 1244, 1246, 1248, 1250} : Set ℤ) ∧
      ∀ d : ℤ, d ∈ ({1240, 1242, 1244, 1246, 1248, 1250} : Set ℤ) →
        ∀ N : ℕ, 0 < partialSingularSeries ({0, d} : Finset ℤ) N := by
  constructor
  · ext d
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      pair_admissible_iff_even]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨k, hk⟩ := h3
      omega
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        refine ⟨by norm_num, by norm_num, ?_⟩ <;> decide
  · intro d hd N
    have : Even d := by
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact partialSingularSeries_pos ((pair_admissible_iff_even d).2 this) N

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

