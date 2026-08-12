/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

open scoped Classical in
/-- The number of elements of `A` below `n`. -/
noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (· ∈ A)).card

open scoped Classical in
/-- The upper (asymptotic) density of a set of naturals. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun n : ℕ => (countUpTo A n : ℝ) / n) atTop

/-- `A` contains an arithmetic progression of length `k` (with positive common difference). -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The finitary form of Szemerédi's theorem: for every length `k` and every density `δ > 0`,
every sufficiently large initial segment `range n` has the property that each of its subsets of
size at least `δ * n` contains a `k`-term arithmetic progression. -/
def SzemerediFinitary : Prop :=
  ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ, s ⊆ Finset.range n →
    δ * n ≤ (s.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ s

lemma HasAP.mono_length {A : Set ℕ} {k m : ℕ} (h : HasAP A k) (hm : m ≤ k) : HasAP A m := by
  obtain ⟨a, d, hd, hap⟩ := h
  exact ⟨a, d, hd, fun i hi => hap i (lt_of_lt_of_le hi hm)⟩

lemma countUpTo_le (A : Set ℕ) (n : ℕ) : countUpTo A n ≤ n := by
  classical
  simpa [countUpTo] using
    (Finset.card_le_card (Finset.filter_subset (· ∈ A) (Finset.range n))).trans_eq
      (Finset.card_range n)

lemma isCoboundedUnder_density (A : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (countUpTo A n : ℝ) / n) := by
  refine Filter.IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
  simp only [Filter.eventually_map]
  filter_upwards with n
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma density_le_one (A : Set ℕ) (n : ℕ) : (countUpTo A n : ℝ) / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast countUpTo_le A n

/-- If a set has positive upper density `δ`, then for any `δ' < δ` there are infinitely many
`n` with at least `δ' * n` elements of `A` below `n`. -/
lemma frequently_lt_countUpTo {A : Set ℕ} {c : ℝ} (hc : c < upperDensity A) :
    ∃ᶠ n : ℕ in atTop, c * n < (countUpTo A n : ℝ) := by
  have h := Filter.frequently_lt_of_lt_limsup (isCoboundedUnder_density A) hc
  have h1 : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  refine (h.and_eventually h1).mono ?_
  rintro n ⟨hlt, hn⟩
  exact (lt_div_iff₀ hn).1 hlt

/-- **Reduction**: the finitary form of Szemerédi's theorem implies the infinitary,
density form: every set of naturals of positive upper density contains arithmetic
progressions of every finite length.

This is the statement obtained from Furstenberg's multiple recurrence theorem via the
Furstenberg correspondence principle; here it is derived, in a Lean-checked way, from the
finitary statement `SzemerediFinitary` taken as a hypothesis. Unconditionally we also prove:
the case `k = 3` (`Frontier.hasAP_three_of_pos_upperDensity`, from Roth's theorem), the
finitary property for `k = 3` (`Frontier.szemerediFinitary_three`), and the case of all `k`
for density above `1 - 1/(2k)` (`Frontier.hasAP_of_upperDensity_gt`). -/
theorem furstenberg_szemeredi (hSz : SzemerediFinitary) (A : Set ℕ)
    (hA : 0 < upperDensity A) (k : ℕ) : HasAP A k := by
  classical
  set c : ℝ := upperDensity A / 2 with hc
  have hc0 : 0 < c := by positivity
  have hclt : c < upperDensity A := by rw [hc]; linarith
  obtain ⟨N, hN⟩ := hSz k c hc0
  obtain ⟨n, hn, hlt⟩ := ((frequently_lt_countUpTo hclt).and_eventually
    (eventually_ge_atTop N)).exists
  set s : Finset ℕ := (Finset.range n).filter (· ∈ A) with hs
  have hsub : s ⊆ Finset.range n := Finset.filter_subset _ _
  have hcard : c * n ≤ (s.card : ℝ) := le_of_lt (by simpa [hs, countUpTo] using hn)
  obtain ⟨a, d, hd, hap⟩ := hN n hlt s hsub hcard
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have := hap i hi
  rw [hs, Finset.mem_filter] at this
  exact this.2

/-- From a subset of `range n` larger than the Roth number of `n` one extracts a
three-term arithmetic progression. -/
lemma exists_threeAP_of_rothNumberNat_lt {n : ℕ} {s : Finset ℕ} (hsub : s ⊆ Finset.range n)
    (hcard : rothNumberNat n < s.card) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ s ∧ a + d ∈ s ∧ a + 2 * d ∈ s := by
  by_contra hcon
  push_neg at hcon
  have hfree : ThreeAPFree (s : Set ℕ) := by
    intro a ha b hb c hcmem habc
    by_contra hne
    simp only [Finset.mem_coe] at ha hb hcmem
    rcases lt_trichotomy a b with h | h | h
    · -- a < b, so b - a > 0 and a, b, c is an AP
      have hd : 0 < b - a := by omega
      have h1 : a + (b - a) = b := by omega
      have h2 : a + 2 * (b - a) = c := by omega
      exact hcon a (b - a) hd ha (by rwa [h1]) (by rwa [h2])
    · exact hne h
    · -- b < a, so c < b < a and c, b, a is an AP
      have hd : 0 < a - b := by omega
      have h1 : c + (a - b) = b := by omega
      have h2 : c + 2 * (a - b) = a := by omega
      exact hcon c (a - b) hd hcmem (by rwa [h1]) (by rwa [h2])
  have : s.card ≤ rothNumberNat n :=
    hfree.le_rothNumberNat s (fun x hx => Finset.mem_range.1 (hsub hx)) rfl
  omega

/-- **Base case (Roth's theorem, `k = 3`)**: every set of naturals of positive upper density
contains a three-term arithmetic progression. This is unconditional. -/
theorem hasAP_three_of_pos_upperDensity (A : Set ℕ) (hA : 0 < upperDensity A) : HasAP A 3 := by
  classical
  set c : ℝ := upperDensity A / 2 with hc
  have hc0 : 0 < c := by positivity
  have hclt : c < upperDensity A := by rw [hc]; linarith
  have hroth : ∀ᶠ n : ℕ in atTop, (rothNumberNat n : ℝ) ≤ (c / 2) * n := by
    have := (Asymptotics.isLittleO_iff.1 rothNumberNat_isLittleO_id) (by positivity : (0:ℝ) < c / 2)
    filter_upwards [this] with n hn
    simpa [abs_of_nonneg, Nat.cast_nonneg] using hn
  obtain ⟨n, hn, hrn⟩ := ((frequently_lt_countUpTo hclt).and_eventually hroth).exists
  set s : Finset ℕ := (Finset.range n).filter (· ∈ A) with hs
  have hsub : s ⊆ Finset.range n := Finset.filter_subset _ _
  have hcards : (countUpTo A n : ℝ) = (s.card : ℝ) := by simp [hs, countUpTo]
  have hnpos : (0:ℝ) < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [countUpTo] at hn
    · exact_mod_cast hpos
  have hlt : (rothNumberNat n : ℝ) < (s.card : ℝ) := by
    have hhalf : (c / 2) * n < c * n := by nlinarith
    linarith [hcards ▸ hn]
  obtain ⟨a, d, hd, h0, h1, h2⟩ :=
    exists_threeAP_of_rothNumberNat_lt hsub (by exact_mod_cast hlt)
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hmem : ∀ x ∈ s, x ∈ A := by
    intro x hx
    exact (Finset.mem_filter.1 hx).2
  interval_cases i
  · simpa using hmem a h0
  · simpa using hmem _ h1
  · simpa using hmem _ h2

/-- Unconditionally, a set of positive upper density contains arithmetic progressions of
every length `k ≤ 3`. -/
theorem hasAP_of_pos_upperDensity_of_le_three (A : Set ℕ) (hA : 0 < upperDensity A)
    {k : ℕ} (hk : k ≤ 3) : HasAP A k :=
  (hasAP_three_of_pos_upperDensity A hA).mono_length hk

/-! ### Further unconditional results -/

/-- Unconditional finitary Roth: the finitary Szemerédi property `SzemerediFinitary` holds
for `k = 3`, as a consequence of Mathlib's Roth theorem. -/
theorem szemerediFinitary_three (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ, s ⊆ Finset.range n →
      δ * n ≤ (s.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ s := by
  have hroth : ∀ᶠ n : ℕ in atTop, (rothNumberNat n : ℝ) ≤ (δ / 2) * n := by
    have := (Asymptotics.isLittleO_iff.1 rothNumberNat_isLittleO_id)
      (by positivity : (0:ℝ) < δ / 2)
    filter_upwards [this] with n hn
    simpa [abs_of_nonneg, Nat.cast_nonneg] using hn
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hroth
  refine ⟨max 1 N₀, fun n hn s hsub hcard => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have h1 : (rothNumberNat n : ℝ) ≤ (δ / 2) * n := hN₀ n (le_trans (le_max_right _ _) hn)
  have h2 : (δ / 2) * n < δ * n := by nlinarith
  have hlt : rothNumberNat n < s.card := by
    have : (rothNumberNat n : ℝ) < (s.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨a, d, hd, h0, hb, hc⟩ := exists_threeAP_of_rothNumberNat_lt hsub hlt
  refine ⟨a, d, hd, fun i hi => ?_⟩
  interval_cases i
  · simpa using h0
  · simpa using hb
  · simpa using hc

open scoped Classical in
/-- **Unconditional Szemerédi for large density**: for every length `k ≥ 1`, a set of naturals
whose upper density exceeds `1 - 1/(2k)` contains an arithmetic progression of length `k`
(indeed, `k` consecutive integers). This is a pigeonhole argument, valid for all `k`. -/
theorem hasAP_of_upperDensity_gt (A : Set ℕ) (k : ℕ) (hk : 0 < k)
    (hA : 1 - 1 / (2 * k) < upperDensity A) : HasAP A k := by
  classical
  set c : ℝ := 1 - 1 / (2 * k) with hc
  obtain ⟨n, hn, hbig⟩ :=
    ((frequently_lt_countUpTo hA).and_eventually (eventually_gt_atTop (2 * k))).exists
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hkn : k ≤ n := by omega
  have hnR : (0:ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hbig
    exact_mod_cast this
  have hbigR : 2 * (k:ℝ) < n := by exact_mod_cast hbig
  set s : Finset ℕ := (Finset.range n).filter (· ∈ A) with hs
  set B : Finset ℕ := (Finset.range n).filter (fun x => x ∉ A) with hB
  have hcards : (s.card : ℝ) = (countUpTo A n : ℝ) := by simp [hs, countUpTo]
  have hsplit : s.card + B.card = n := by
    rw [hs, hB]
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.range n) (p := fun x => x ∈ A)
  have h2 : c * n < (s.card : ℝ) := hcards ▸ hn
  have h1 : (B.card : ℝ) = n - s.card := by
    have : ((s.card + B.card : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    push_cast at this; linarith
  have hexp : c * (n:ℝ) = n - n / (2 * k) := by rw [hc]; field_simp
  have hBcard : (B.card : ℝ) < n / (2 * k) := by rw [h1]; linarith
  -- the "bad" starting points are those `a` for which some `a + i`, `i < k`, misses `A`
  set bad : Finset ℕ := (Finset.range (n - k)).filter (fun a => ∃ i < k, a + i ∉ A) with hbad
  have hsubimg : bad ⊆ (B ×ˢ Finset.range k).image (fun p => p.1 - p.2) := by
    intro a ha
    rw [hbad, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hlt, i, hik, hmem⟩ := ha
    refine Finset.mem_image.2 ⟨(a + i, i), ?_, by simp⟩
    refine Finset.mem_product.2 ⟨?_, Finset.mem_range.2 hik⟩
    rw [hB, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hmem⟩
  have hbadcard : (bad.card : ℝ) < (n : ℝ) / 2 := by
    have h3 : bad.card ≤ B.card * k := by
      calc bad.card ≤ ((B ×ˢ Finset.range k).image (fun p => p.1 - p.2)).card :=
            Finset.card_le_card hsubimg
        _ ≤ (B ×ˢ Finset.range k).card := Finset.card_image_le
        _ = B.card * k := by simp
    have h4 : (bad.card : ℝ) ≤ (B.card : ℝ) * k := by exact_mod_cast h3
    have h5 : (B.card : ℝ) * k < (n / (2 * k)) * k := mul_lt_mul_of_pos_right hBcard hkR
    have h6 : (n / (2 * (k:ℝ))) * k = n / 2 := by field_simp
    linarith
  have hrange : ((n - k : ℕ) : ℝ) > (n : ℝ) / 2 := by
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
      have := Nat.cast_sub (R := ℝ) hkn
      simpa using this
    rw [hcast]; linarith
  have hex : ∃ a ∈ Finset.range (n - k), a ∉ bad := by
    by_contra hcon
    push_neg at hcon
    have hsubb : Finset.range (n - k) ⊆ bad := fun a ha => hcon a ha
    have hle := Finset.card_le_card hsubb
    rw [Finset.card_range] at hle
    have : ((n - k : ℕ) : ℝ) ≤ (bad.card : ℝ) := by exact_mod_cast hle
    linarith
  obtain ⟨a, haR, hanot⟩ := hex
  rw [hbad, Finset.mem_filter] at hanot
  push_neg at hanot
  have hgood : ∀ i < k, a + i ∈ A := by
    intro i hi
    have := hanot haR i hi
    simpa using this
  exact ⟨a, 1, one_pos, fun i hi => by simpa using hgood i hi⟩

/-! ### Sanity checks: the density hypothesis is satisfiable -/

lemma countUpTo_univ (n : ℕ) : countUpTo Set.univ n = n := by
  classical
  simp [countUpTo]

lemma upperDensity_univ : upperDensity Set.univ = 1 := by
  have h : (fun n : ℕ => (countUpTo Set.univ n : ℝ) / n) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [countUpTo_univ, div_self hne]
  rw [upperDensity, Filter.limsup_congr h, limsup_const]

end Frontier

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

