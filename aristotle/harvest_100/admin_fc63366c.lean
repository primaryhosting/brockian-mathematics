/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series `𝔖(H)` of the tuple `H` is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the quantity `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/
noncomputable def resCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun h : ℤ => (h : ZMod p))).card

/-- Admissibility says exactly that `ν_p(H) < p` for every prime `p`. -/
theorem admissible_iff_resCount_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → resCount H p < p := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : (H.image (fun h : ℤ => (h : ZMod p))) ⊆ (Finset.univ : Finset (ZMod p)).erase r := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hr h hh, Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, ZMod.card p] at hcard
    have hp0 : 0 < p := hp.pos
    exact lt_of_le_of_lt hcard (by omega)
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_contra hcon
    push_neg at hcon
    have huniv : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
      refine Finset.eq_univ_of_forall ?_
      intro r
      obtain ⟨h, hh, hhr⟩ := hcon r
      exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
    have := hH p hp
    rw [resCount, huniv, Finset.card_univ, ZMod.card p] at this
    omega

/-- The local factor of the Hardy–Littlewood singular series of a `k`-tuple `H` at the prime `p`:
`(1 - ν_p(H)/p) / (1 - 1/p)^k`. -/
noncomputable def singularFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (resCount H p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ H.card

/-- For an admissible tuple every local factor of the singular series is strictly positive;
in particular no factor vanishes. -/
theorem singularFactor_pos (H : Finset ℤ) (hH : Admissible H) (p : ℕ) (hp : p.Prime) :
    0 < singularFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt : (resCount H p : ℝ) < (p : ℝ) := by
    exact_mod_cast (admissible_iff_resCount_lt H).mp hH p hp
  have hnum : 0 < 1 - (resCount H p : ℝ) / (p : ℝ) := by
    have : (resCount H p : ℝ) / (p : ℝ) < 1 := (div_lt_one hp0).mpr hlt
    linarith
  have hden : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- A tuple with fewer than `p` elements always misses a residue class modulo `p`. -/
theorem exists_missing_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨by omega⟩
  by_contra hcon
  push_neg at hcon
  have huniv : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
    refine Finset.eq_univ_of_forall ?_
    intro r
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have hcard : (Finset.univ : Finset (ZMod p)).card ≤ H.card := by
    rw [← huniv]; exact Finset.card_image_le
  rw [Finset.card_univ, ZMod.card p] at hcard
  omega

/-- A tuple all of whose elements are prime to `p` misses the residue class `0` modulo `p`. -/
theorem exists_missing_residue_of_not_dvd (H : Finset ℤ) (p : ℕ)
    (hp : ∀ h ∈ H, ¬ ((p : ℤ) ∣ h)) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  refine ⟨0, fun h hh hcon => hp h hh ?_⟩
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hcon

/-- **Admissible gap ranges from arithmetic progressions with primorial common difference.**
For any `k` and any integer `a` prime to all primes `p ≤ k`, the `k`-term arithmetic progression
`a, a + k#, a + 2·k#, …, a + (k-1)·k#` (common difference the primorial `k#`) is an admissible
tuple. -/
theorem admissible_primorial_progression (k : ℕ) (a : ℤ)
    (ha : ∀ p : ℕ, p.Prime → p ≤ k → ¬ ((p : ℤ) ∣ a)) :
    Admissible ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))) := by
  intro p hp
  by_cases hpk : p ≤ k
  · -- small primes: every element is `≡ a (mod p)`, and `p ∤ a`
    refine exists_missing_residue_of_not_dvd _ p ?_
    intro h hh
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
    have hdvd : (p : ℤ) ∣ (primorial k : ℤ) := by
      have : p ∣ primorial k := by
        refine Finset.dvd_prod_of_mem (fun q => q) ?_
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp⟩
      exact_mod_cast Int.natCast_dvd_natCast.mpr this
    intro hcon
    exact ha p hp hpk (by
      have : (p : ℤ) ∣ (i : ℤ) * (primorial k : ℤ) := hdvd.mul_left _
      simpa using (dvd_sub hcon this))
  · -- large primes: the tuple has fewer than `p` elements
    refine exists_missing_residue_of_card_lt _ p ?_
    have : ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))).card ≤ k :=
      le_trans Finset.card_image_le (le_of_eq (Finset.card_range k))
    omega

/-- The progression really has `k` distinct terms (the common difference `k#` is positive). -/
theorem card_primorial_progression (k : ℕ) (a : ℤ) :
    ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))).card = k := by
  have hpos : (0 : ℤ) < (primorial k : ℤ) := by
    exact_mod_cast primorial_pos k
  have hinj : Set.InjOn (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))
      (Finset.range k : Finset ℕ) := by
    intro i _ j _ hij
    simp only at hij
    have h : (i : ℤ) * (primorial k : ℤ) = (j : ℤ) * (primorial k : ℤ) := by linarith
    have := mul_right_cancel₀ (ne_of_gt hpos) h
    exact_mod_cast this
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **Singular Series Gaps 7280.**
A new family of admissible gap ranges of length `7280`: for every integer `a` that is prime to
all primes `p ≤ 7280`, the `7280`-term arithmetic progression with common difference the
primorial `7280#`,
`a, a + 7280#, a + 2·7280#, …, a + 7279·7280#`,
consists of `7280` distinct integers and is an admissible tuple, i.e. for every prime `p` it
omits a residue class modulo `p`.  Consequently its Hardy–Littlewood singular series is nonzero. -/
theorem SingularSeriesGaps7280 (a : ℤ)
    (ha : ∀ p : ℕ, p.Prime → p ≤ 7280 → ¬ ((p : ℤ) ∣ a)) :
    ((Finset.range 7280).image (fun i : ℕ => a + (i : ℤ) * (primorial 7280 : ℤ))).card = 7280 ∧
      Admissible ((Finset.range 7280).image (fun i : ℕ => a + (i : ℤ) * (primorial 7280 : ℤ))) :=
  ⟨card_primorial_progression 7280 a, admissible_primorial_progression 7280 a ha⟩

/-- Every local factor of the Hardy–Littlewood singular series of the length-`7280` gap range
`{a + i·7280# : i < 7280}` is strictly positive. -/
theorem singularFactor_pos_gaps7280 (a : ℤ)
    (ha : ∀ p : ℕ, p.Prime → p ≤ 7280 → ¬ ((p : ℤ) ∣ a)) (p : ℕ) (hp : p.Prime) :
    0 < singularFactor
      ((Finset.range 7280).image (fun i : ℕ => a + (i : ℤ) * (primorial 7280 : ℤ))) p :=
  singularFactor_pos _ (admissible_primorial_progression 7280 a ha) p hp

/-- The special case `a = 1` of `Brockian.SingularSeriesGaps7280`. -/
theorem SingularSeriesGaps7280_one :
    ((Finset.range 7280).image (fun i : ℕ => 1 + (i : ℤ) * (primorial 7280 : ℤ))).card = 7280 ∧
      Admissible ((Finset.range 7280).image (fun i : ℕ => 1 + (i : ℤ) * (primorial 7280 : ℤ))) := by
  refine SingularSeriesGaps7280 1 ?_
  intro p hp _ hdvd
  have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have h2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  linarith

end Brockian

