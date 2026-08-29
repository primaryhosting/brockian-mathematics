import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

set_option grind.warning false

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/
def residues (H : Finset ℕ) (p : ℕ) : Finset ℕ := H.image (fun h => h % p)

/-- `localCount H p` is the number of residue classes modulo `p` occupied by `H`;
this is the quantity `ν_p(H)` appearing in the Euler factors of the singular series. -/
def localCount (H : Finset ℕ) (p : ℕ) : ℕ := (residues H p).card

/-- A tuple `H` of naturals is *admissible* if for every prime `p` it misses at least one
residue class modulo `p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- The arithmetic-progression gap tuple `{a, a + d, a + 2d, …, a + (k-1)d}`. -/
def gapTuple (a d k : ℕ) : Finset ℕ := (Finset.range k).image (fun i => a + i * d)

lemma residues_subset_range (H : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    residues H p ⊆ Finset.range p := by
  intro r hr
  simp only [residues, Finset.mem_image] at hr
  obtain ⟨h, _, rfl⟩ := hr
  exact Finset.mem_range.mpr (Nat.mod_lt _ hp)

/-- Admissibility is equivalent to the local counts being strictly smaller than the modulus. -/
lemma admissible_iff (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → localCount H p < p := by
  constructor
  · intro hH p hp
    obtain ⟨r, hrp, hr⟩ := hH p hp
    have hsub : residues H p ⊆ (Finset.range p).erase r := by
      intro s hs
      have hs' := residues_subset_range H hp.pos hs
      refine Finset.mem_erase.mpr ⟨?_, hs'⟩
      simp only [residues, Finset.mem_image] at hs
      obtain ⟨h, hh, rfl⟩ := hs
      exact hr h hh
    have hcard : ((Finset.range p).erase r).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hrp), Finset.card_range]
    have hle : localCount H p ≤ p - 1 := by
      simpa [localCount, hcard] using Finset.card_le_card hsub
    have hp1 : 2 ≤ p := hp.two_le
    omega
  · intro hH p hp
    have hlt : (residues H p).card < (Finset.range p).card := by
      simpa [localCount, Finset.card_range] using hH p hp
    obtain ⟨r, hr, hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨r, Finset.mem_range.mp hr, ?_⟩
    intro h hh hcon
    exact hr' (by simp only [residues, Finset.mem_image]; exact ⟨h, hh, hcon⟩)

lemma localCount_le_card (H : Finset ℕ) (p : ℕ) : localCount H p ≤ H.card :=
  Finset.card_image_le

lemma card_gapTuple_le (a d k : ℕ) : (gapTuple a d k).card ≤ k := by
  simpa [gapTuple] using
    (Finset.card_image_le (s := Finset.range k) (f := fun i => a + i * d)).trans_eq
      (Finset.card_range k)

/-- If `p ∣ d` then every element of the progression lies in the single class `a mod p`. -/
lemma localCount_gapTuple_of_dvd {a d k p : ℕ} (hk : 0 < k) (hpd : p ∣ d) :
    localCount (gapTuple a d k) p = 1 := by
  have hres : residues (gapTuple a d k) p = {a % p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · simp only [residues, Finset.mem_image, gapTuple]
      exact ⟨a, ⟨0, Finset.mem_range.mpr hk, by simp⟩, rfl⟩
    · intro r hr
      simp only [residues, gapTuple, Finset.mem_image, Finset.mem_range] at hr
      obtain ⟨h, ⟨i, _, rfl⟩, rfl⟩ := hr
      obtain ⟨c, rfl⟩ := hpd
      simp [Nat.mul_left_comm, Nat.add_mul_mod_self_left]
  simp [localCount, hres]

/-- The gap range: every element of the tuple lies in the interval `[a, a + (k-1)d]`,
and both endpoints are attained (for `k > 0`), so the diameter is exactly `(k-1)·d`. -/
lemma gapTuple_gap_range (a d k : ℕ) (hk : 0 < k) :
    (∀ h ∈ gapTuple a d k, a ≤ h ∧ h ≤ a + (k - 1) * d) ∧
      a ∈ gapTuple a d k ∧ a + (k - 1) * d ∈ gapTuple a d k := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    simp only [gapTuple, Finset.mem_image, Finset.mem_range] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    exact ⟨Nat.le_add_right _ _,
      Nat.add_le_add_left (Nat.mul_le_mul_right d (by omega)) a⟩
  · simp only [gapTuple, Finset.mem_image, Finset.mem_range]
    exact ⟨0, hk, by simp⟩
  · simp only [gapTuple, Finset.mem_image, Finset.mem_range]
    exact ⟨k - 1, by omega, rfl⟩

/--
**Singular Series Gaps 13501360.**

Let `k ≥ 1` and let `d` be divisible by every prime `p ≤ k`.  Then the length-`k`
arithmetic progression `{a, a+d, …, a+(k-1)d}` is an admissible tuple, and consequently
every Euler factor `1 - ν_p(H)/p` of its singular series is strictly positive.

This gives an infinite family of admissible gap ranges: the diameter of the tuple is
`(k-1)·d`, and the conclusion holds for every shift `a`.
-/
theorem SingularSeriesGaps13501360 (a d k : ℕ) (hk : 0 < k)
    (hd : ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d) :
    Admissible (gapTuple a d k) ∧
      ∀ p : ℕ, p.Prime → 0 < 1 - (localCount (gapTuple a d k) p : ℝ) / p := by
  have key : ∀ p : ℕ, p.Prime → localCount (gapTuple a d k) p < p := by
    intro p hp
    by_cases hpk : p ≤ k
    · rw [localCount_gapTuple_of_dvd hk (hd p hp hpk)]
      exact hp.one_lt
    · have h1 : localCount (gapTuple a d k) p ≤ k :=
        (localCount_le_card _ p).trans (card_gapTuple_le a d k)
      omega
  refine ⟨(admissible_iff _).mpr key, ?_⟩
  intro p hp
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlt : (localCount (gapTuple a d k) p : ℝ) < p := by exact_mod_cast key p hp
  have : (localCount (gapTuple a d k) p : ℝ) / p < 1 := (div_lt_one hppos).mpr hlt
  linarith

/-- A concrete new admissible gap range: the 13-element progression starting at `13501360`
with common difference `30030 = 2·3·5·7·11·13`, of diameter `360360`. -/
theorem SingularSeriesGaps13501360_instance :
    Admissible (gapTuple 13501360 30030 13) ∧
      ∀ p : ℕ, p.Prime → 0 < 1 - (localCount (gapTuple 13501360 30030 13) p : ℝ) / p := by
  refine SingularSeriesGaps13501360 13501360 30030 13 (by norm_num) ?_
  intro p hp hple
  interval_cases p <;> revert hp <;> decide

end Brockian

