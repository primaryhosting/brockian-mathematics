import Mathlib

/-!
# Admissible gap ranges and the local factors of the singular series

A finite set `H ⊆ ℤ` (a *tuple*) is **admissible** when, for every prime `p`, the reductions
of the elements of `H` modulo `p` do not cover all of `ℤ/pℤ`.  This is exactly the condition
that every local factor

`localFactor H p = (1 - ν_H(p)/p) * (1 - 1/p)^(-|H|)`

of the Hardy–Littlewood singular series `𝔖(H) = ∏_p localFactor H p` is nonzero (equivalently,
positive), where `ν_H(p)` is the number of residue classes mod `p` occupied by `H`.

A **gap range** is a tuple of the shape `{a, a + d, a + 2d, …, a + (k-1)d}`: `k` points with
constant gap `d`.  The main results characterise which gap ranges are admissible, and in
particular determine all admissible gap ranges of diameter `7280`.
-/

namespace Brockian

/-- The set of residue classes mod `p` occupied by a tuple `H ⊆ ℤ`. -/
def residues (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℤ => (Int.cast h : ZMod p))

/-- A tuple `H ⊆ ℤ` is *admissible* if for every prime `p` it misses at least one residue
class modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (residues H p).card < p

/-- The local factor at `p` of the Hardy–Littlewood singular series of the tuple `H`. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - ((residues H p).card : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- A *gap range*: the `k`-tuple `{a, a + d, …, a + (k-1)d}` with first term `a` and gap `d`. -/
def gapSet (a d : ℤ) (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun j : ℕ => a + (j : ℤ) * d)

/-- The number of occupied residue classes is at most the size of the tuple. -/
lemma card_residues_le (H : Finset ℤ) (p : ℕ) : (residues H p).card ≤ H.card :=
  Finset.card_image_le

/-- Modulo a prime `p` a tuple occupies at most `p` residue classes. -/
lemma card_residues_le_prime (H : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    (residues H p).card ≤ p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := Finset.card_le_univ (residues H p)
  simpa [ZMod.card] using h

/-- The local factor at a prime `p` is positive exactly when `H` misses a class mod `p`. -/
lemma localFactor_pos_iff (H : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p ↔ (residues H p).card < p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left <;> linarith
    linarith
  have hzp : 0 < (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ)) := zpow_pos h1 _
  rw [localFactor, mul_pos_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have : ((residues H p).card : ℝ) < p := by
        rw [sub_pos, div_lt_one hp0] at h; exact h
      exact_mod_cast this
    · linarith
  · intro h
    refine Or.inl ⟨?_, hzp⟩
    rw [sub_pos, div_lt_one hp0]
    exact_mod_cast h

/-- The local factor at a prime `p` is nonzero exactly when `H` misses a class mod `p`. -/
lemma localFactor_ne_zero_iff (H : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    localFactor H p ≠ 0 ↔ (residues H p).card < p := by
  refine ⟨fun h => ?_, fun h => ne_of_gt ((localFactor_pos_iff H hp).2 h)⟩
  by_contra hc
  push_neg at hc
  have hcard : (residues H p).card = p := le_antisymm (card_residues_le_prime H hp) hc
  have hp0 : (0 : ℝ) < p := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  apply h
  rw [localFactor, hcard, div_self (ne_of_gt hp0)]
  ring

/-- Admissibility is exactly the nonvanishing (equivalently, positivity) of all the local
factors of the singular series. -/
theorem admissible_iff_localFactor_pos (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → 0 < localFactor H p :=
  ⟨fun h p hp => (localFactor_pos_iff H hp).2 (h p hp),
   fun h p hp => (localFactor_pos_iff H hp).1 (h p hp)⟩

/-- Admissibility is exactly the nonvanishing of all the local factors. -/
theorem admissible_iff_localFactor_ne_zero (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → localFactor H p ≠ 0 :=
  ⟨fun h p hp => (localFactor_ne_zero_iff H hp).2 (h p hp),
   fun h p hp => (localFactor_ne_zero_iff H hp).1 (h p hp)⟩

/-- If `p ∣ d` then a gap range with gap `d` occupies exactly one residue class mod `p`. -/
lemma residues_gapSet_of_dvd {a d : ℤ} {k p : ℕ} (hk : 0 < k) (hp : (p : ℤ) ∣ d) :
    residues (gapSet a d k) p = {(a : ZMod p)} := by
  have hd0 : ((d : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).2 hp
  have hcongr : residues (gapSet a d k) p
      = (Finset.range k).image (fun _ : ℕ => (a : ZMod p)) := by
    rw [residues, gapSet, Finset.image_image]
    refine Finset.image_congr ?_
    intro j _
    simp [Function.comp, hd0]
  rw [hcongr, Finset.image_const]
  exact Finset.nonempty_range_iff.2 hk.ne'

/-- If `p ∤ d` and `p ≤ k` then a gap range with gap `d` occupies every residue class mod `p`. -/
lemma residues_gapSet_of_not_dvd {a d : ℤ} {k p : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (hd : ¬ ((p : ℤ) ∣ d)) : (residues (gapSet a d k) p).card = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdne : ((d : ℤ) : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hd
  have huniv : residues (gapSet a d k) p = Finset.univ := by
    refine Finset.eq_univ_of_forall ?_
    intro x
    set u : ZMod p := (x - (a : ZMod p)) * ((d : ℤ) : ZMod p)⁻¹ with hu
    have hj : u.val < k := lt_of_lt_of_le (ZMod.val_lt u) hpk
    rw [residues, gapSet, Finset.image_image]
    refine Finset.mem_image.2 ⟨u.val, Finset.mem_range.2 hj, ?_⟩
    have hval : ((u.val : ℕ) : ZMod p) = u := ZMod.natCast_rightInverse u
    simp only [Function.comp_apply]
    push_cast
    rw [hval, hu]
    field_simp
    ring
  rw [huniv]
  simp [ZMod.card]

/-- **Characterisation of admissible gap ranges.**  A nonempty gap range with gap `d` and `k`
terms is admissible precisely when every prime `p ≤ k` divides the gap `d`. -/
theorem admissible_gapSet_iff (a d : ℤ) (k : ℕ) (hk : 0 < k) :
    Admissible (gapSet a d k) ↔ ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d := by
  constructor
  · intro h p hp hpk
    by_contra hd
    have hcard := residues_gapSet_of_not_dvd (a := a) hp hpk hd
    have hlt := h p hp
    omega
  · intro h p hp
    by_cases hd : (p : ℤ) ∣ d
    · rw [residues_gapSet_of_dvd hk hd]
      simpa using hp.one_lt
    · have hpk : k < p := by
        by_contra hc
        exact hd (h p hp (not_lt.1 hc))
      calc (residues (gapSet a d k) p).card ≤ (gapSet a d k).card := card_residues_le _ _
        _ ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
        _ < p := hpk

/-- Every gap range of two terms with an even gap is admissible. -/
theorem admissible_gapSet_two {a d : ℤ} (hd : (2 : ℤ) ∣ d) : Admissible (gapSet a d 2) := by
  refine (admissible_gapSet_iff a d 2 (by norm_num)).2 ?_
  intro p hp hp2
  interval_cases p
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact_mod_cast hd

/-- A gap range with three or more terms and diameter `D` forces `6 ∣ D`. -/
theorem six_dvd_diameter_of_admissible {a d : ℤ} {k : ℕ} (hk : 3 ≤ k)
    (h : Admissible (gapSet a d k)) : (6 : ℤ) ∣ d * ((k : ℤ) - 1) := by
  have hk0 : 0 < k := by omega
  have hall := (admissible_gapSet_iff a d k hk0).1 h
  have h2 : (2 : ℤ) ∣ d := by exact_mod_cast hall 2 (by norm_num) (by omega)
  have h3 : (3 : ℤ) ∣ d := by exact_mod_cast hall 3 (by norm_num) (by omega)
  have h6 : (6 : ℤ) ∣ d := by omega
  exact h6.mul_right _

/-- **Primorial form of the characterisation.**  A nonempty gap range is admissible exactly
when its gap is divisible by the primorial `k#` (the product of all primes `≤ k`). -/
theorem admissible_gapSet_iff_primorial_dvd (a d : ℤ) (k : ℕ) (hk : 0 < k) :
    Admissible (gapSet a d k) ↔ ((primorial k : ℕ) : ℤ) ∣ d := by
  rw [admissible_gapSet_iff a d k hk]
  constructor
  · intro h
    refine Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr ?_)
    refine Finset.prod_primes_dvd _ (fun q hq => (Finset.mem_filter.1 hq).2.prime) (fun q hq => ?_)
    rw [Finset.mem_filter, Finset.mem_range] at hq
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (h q hq.2 (by omega)))
  · intro h p hp hpk
    have hdvd : p ∣ primorial k :=
      Finset.dvd_prod_of_mem _ (by simp [Finset.mem_filter, Finset.mem_range, hp]; omega)
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) h

/-- A two-term gap range is the pair `{a, a + d}`. -/
lemma gapSet_two (a d : ℤ) : gapSet a d 2 = {a, a + d} := by
  ext x
  simp [gapSet, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

/-- **Admissible gap ranges of a given diameter.**  If the diameter `D` is even but not
divisible by `3`, then among gap ranges of diameter `D` with at least two terms exactly the
two-term ones (the pairs `{a, a + D}`) are admissible. -/
theorem admissible_gapSet_of_diameter_iff {D : ℤ} (h2 : (2 : ℤ) ∣ D) (h3 : ¬ ((3 : ℤ) ∣ D))
    (a d : ℤ) (k : ℕ) (hk : 2 ≤ k) (hdiam : d * ((k : ℤ) - 1) = D) :
    Admissible (gapSet a d k) ↔ k = 2 := by
  constructor
  · intro hadm
    by_contra hne
    have hk3 : 3 ≤ k := by omega
    have hd3 : (3 : ℤ) ∣ d :=
      (admissible_gapSet_iff a d k (by omega)).1 hadm 3 (by norm_num) hk3
    exact h3 (hdiam ▸ hd3.mul_right _)
  · rintro rfl
    have hd : d = D := by
      have : d * ((2 : ℤ) - 1) = D := by exact_mod_cast hdiam
      linarith
    subst hd
    exact admissible_gapSet_two h2

/-- **All admissible gap ranges of diameter `7280`.**

For a gap range with `k ≥ 2` terms, gap `d` and diameter `d * (k - 1) = 7280`, admissibility
holds if and only if `k = 2`; that is, the only admissible gap ranges of diameter `7280` with
at least two terms are the pairs `{a, a + 7280}`.  Moreover all local factors of the singular
series of such a pair are positive. -/
theorem SingularSeriesGaps7280 :
    (∀ (a d : ℤ) (k : ℕ), 2 ≤ k → d * ((k : ℤ) - 1) = 7280 →
        (Admissible (gapSet a d k) ↔ k = 2)) ∧
      (∀ a : ℤ, ∀ p : ℕ, p.Prime → 0 < localFactor (gapSet a 7280 2) p) := by
  have hpair : ∀ a : ℤ, Admissible (gapSet a 7280 2) :=
    fun a => admissible_gapSet_two (by norm_num)
  exact ⟨fun a d k hk2 hdiam =>
      admissible_gapSet_of_diameter_iff (by norm_num) (by decide) a d k hk2 hdiam,
    fun a => (admissible_iff_localFactor_pos _).1 (hpair a)⟩

/-- Explicit form of the admissible gap ranges of diameter `7280`: every pair
`{a, a + 7280}` is admissible. -/
theorem admissible_pair_7280 (a : ℤ) : Admissible ({a, a + 7280} : Finset ℤ) := by
  rw [← gapSet_two]
  exact admissible_gapSet_two (by norm_num)

end Brockian

import Mathlib
import RequestProject.SingularSeriesGaps

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

