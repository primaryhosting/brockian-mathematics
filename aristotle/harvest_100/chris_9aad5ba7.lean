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

/-- The residues modulo `p` covered by the tuple `H`. -/
def coveredResidues (H : Finset ℕ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℕ => (h : ZMod p))

/-- A tuple `H` is *admissible* if for every prime `p` it misses at least one residue class
modulo `p`.  This is exactly the condition for the singular series of `H` to be nonzero. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The local factor of the singular series at `p`, up to the (nonzero) normalisation
`(1 - 1/p)^{-|H|}`: it is `1 - ν_H(p)/p`, where `ν_H(p)` is the number of residue classes
modulo `p` occupied by `H`. -/
def singularFactor (H : Finset ℕ) (p : ℕ) : ℚ :=
  1 - ((coveredResidues H p).card : ℚ) / (p : ℚ)

/-- The arithmetic-progression tuple `{0, d, 2d, …, (k-1)d}`. -/
def apTuple (k d : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => i * d)

theorem mem_coveredResidues {H : Finset ℕ} {p : ℕ} {r : ZMod p} :
    r ∈ coveredResidues H p ↔ ∃ h ∈ H, (h : ZMod p) = r := by
  simp [coveredResidues]

/-- Admissibility is exactly the statement that some residue class mod `p` is missed,
phrased via the cardinality of the covered set. -/
theorem card_coveredResidues_lt_iff {H : Finset ℕ} {p : ℕ} [NeZero p] :
    (coveredResidues H p).card < p ↔ ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hcard
    by_contra hcon
    push_neg at hcon
    have huniv : coveredResidues H p = Finset.univ := by
      refine Finset.eq_univ_of_forall (fun r => ?_)
      obtain ⟨h, hh, hr⟩ := hcon r
      exact mem_coveredResidues.mpr ⟨h, hh, hr⟩
    rw [huniv, Finset.card_univ, ZMod.card] at hcard
    exact lt_irrefl _ hcard
  · rintro ⟨r, hr⟩
    have hne : r ∉ coveredResidues H p := by
      intro hmem
      obtain ⟨h, hh, rfl⟩ := mem_coveredResidues.mp hmem
      exact hr h hh rfl
    have hss : coveredResidues H p ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr (fun hcon => hne (hcon ▸ Finset.mem_univ r))
    have := Finset.card_lt_card hss
    rwa [Finset.card_univ, ZMod.card] at this

/-- Admissibility is equivalent to the non-vanishing of every local singular-series factor. -/
theorem admissible_iff_singularFactor_ne_zero (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → singularFactor H p ≠ 0 := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (coveredResidues H p).card < p := card_coveredResidues_lt_iff.mpr (hH p hp)
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
    intro hzero
    rw [singularFactor, sub_eq_zero, eq_div_iff (ne_of_gt hp0), one_mul] at hzero
    have : (coveredResidues H p).card = p := by exact_mod_cast hzero.symm
    omega
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    refine card_coveredResidues_lt_iff.mp ?_
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
    have hle : (coveredResidues H p).card ≤ p := by
      simpa [ZMod.card] using Finset.card_le_univ (coveredResidues H p)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      refine hH p hp ?_
      rw [singularFactor, h, div_self (ne_of_gt hp0), sub_self]

/-- The residues covered by an arithmetic progression tuple. -/
theorem coveredResidues_apTuple (k d p : ℕ) :
    coveredResidues (apTuple k d) p
      = (Finset.range k).image (fun i : ℕ => (i : ZMod p) * (d : ZMod p)) := by
  ext r
  simp only [mem_coveredResidues, apTuple, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, by push_cast; ring⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i * d, ⟨i, hi, rfl⟩, by push_cast; ring⟩

/-- **Admissibility criterion for arithmetic progressions.**
The tuple `{0, d, 2d, …, (k-1)d}` is admissible iff every prime `p ≤ k` divides `d`. -/
theorem admissible_apTuple_iff (k d : ℕ) :
    Admissible (apTuple k d) ↔ ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d := by
  constructor
  · intro hadm p hp hpk
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := hadm p hp
    by_contra hdvd
    have hd : (d : ZMod p) ≠ 0 := fun hc => hdvd ((ZMod.natCast_eq_zero_iff d p).mp hc)
    set i : ℕ := (r * (d : ZMod p)⁻¹).val with hi
    have hilt : i < p := ZMod.val_lt _
    have hmem : i * d ∈ apTuple k d :=
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le hilt hpk), rfl⟩
    refine hr (i * d) hmem ?_
    push_cast
    rw [hi, ZMod.natCast_val, ZMod.cast_id]
    field_simp
  · intro hdvd p hp
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_cases hpk : p ≤ k
    · -- all elements are `≡ 0 mod p`; the class of `1` is missed
      have hd : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr (hdvd p hp hpk)
      refine ⟨1, fun h hh => ?_⟩
      simp only [apTuple, Finset.mem_image, Finset.mem_range] at hh
      obtain ⟨i, _, rfl⟩ := hh
      push_cast
      rw [hd, mul_zero]
      exact fun hcon => one_ne_zero hcon.symm
    · -- fewer than `p` residues are covered
      push_neg at hpk
      refine card_coveredResidues_lt_iff.mp ?_
      calc (coveredResidues (apTuple k d) p).card
          ≤ (Finset.range k).card := by
            rw [coveredResidues_apTuple]; exact Finset.card_image_le
        _ = k := Finset.card_range k
        _ < p := hpk

/-- **Singular Series Gaps 7280.**

1.  A complete criterion for the admissibility of arithmetic-progression tuples
    `{0, d, 2d, …, (k-1)d}`: admissible exactly when every prime `p ≤ k` divides `d`.
2.  Equivalently, admissibility is the non-vanishing of all local singular-series factors.
3.  For the gap `d = 7280 = 2^4 · 5 · 7 · 13` the admissible lengths are exactly `k ≤ 2`.
4.  For the gap `d = 21840 = 3 · 7280 = 2^4 · 3 · 5 · 7 · 13` the admissible lengths extend
    all the way to `k ≤ 10`.
-/
theorem SingularSeriesGaps7280 :
    (∀ k d : ℕ, Admissible (apTuple k d) ↔ ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d) ∧
    (∀ H : Finset ℕ, Admissible H ↔ ∀ p : ℕ, p.Prime → singularFactor H p ≠ 0) ∧
    (∀ k : ℕ, Admissible (apTuple k 7280) ↔ k ≤ 2) ∧
    (∀ k : ℕ, Admissible (apTuple k 21840) ↔ k ≤ 10) := by
  refine ⟨admissible_apTuple_iff, admissible_iff_singularFactor_ne_zero, ?_, ?_⟩
  · intro k
    rw [admissible_apTuple_iff]
    constructor
    · intro h
      by_contra hk
      push_neg at hk
      have := h 3 (by norm_num) (by omega)
      norm_num at this
    · intro hk p hp hpk
      have hp2 : 2 ≤ p := hp.two_le
      have : p = 2 := by omega
      subst this
      norm_num
  · intro k
    rw [admissible_apTuple_iff]
    constructor
    · intro h
      by_contra hk
      push_neg at hk
      have := h 11 (by norm_num) (by omega)
      norm_num at this
    · intro hk p hp hpk
      have hp2 : 2 ≤ p := hp.two_le
      have hple : p ≤ 10 := le_trans hpk hk
      interval_cases p <;> revert hp <;> decide

end Brockian

