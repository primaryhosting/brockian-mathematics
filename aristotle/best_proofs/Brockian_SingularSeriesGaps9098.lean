import Mathlib

/-!
# Admissible arithmetic-progression gap tuples

A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood prime
`k`-tuples conjecture) when, for every prime `p`, the reduction of `H` mod `p` omits at least
one residue class.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime.

This file characterises admissibility of the arithmetic progression tuples
`{0, d, 2d, …, (k-1)d}` and derives new admissible gap ranges for `90 ≤ k ≤ 98`.
-/

open scoped BigOperators

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if for every prime `p` it omits at least one
residue class modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The `k`-term arithmetic progression tuple with common difference `d`, i.e. the gap pattern
`{0, d, 2d, …, (k-1)d}`. -/
def apTuple (k : ℕ) (d : ℤ) : Finset ℤ :=
  (Finset.range k).image (fun j : ℕ => (j : ℤ) * d)

lemma card_apTuple_le (k : ℕ) (d : ℤ) : (apTuple k d).card ≤ k := by
  rw [apTuple]
  exact le_trans Finset.card_image_le (by simp)

/-- A set with fewer than `p` elements always omits a residue class mod `p`. -/
lemma exists_residue_notMem_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have huniv : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr ?_
    intro r
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ H.card := by
    rw [← huniv]; exact Finset.card_image_le
  rw [Finset.card_univ, ZMod.card] at h1
  omega

/-- **Characterisation of admissible AP gap tuples.**  The progression
`{0, d, 2d, …, (k-1)d}` is admissible if and only if every prime `p ≤ k` divides `d`. -/
theorem admissible_apTuple_iff (k : ℕ) (d : ℤ) :
    Admissible (apTuple k d) ↔ ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d := by
  constructor
  · intro hadm p hp hpk
    by_contra hdvd
    obtain ⟨r, hr⟩ := hadm p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hd : (d : ZMod p) ≠ 0 := by
      intro h0
      exact hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h0)
    set j : ℕ := (r * (d : ZMod p)⁻¹).val with hj
    have hjlt : j < p := ZMod.val_lt _
    have hmem : ((j : ℤ) * d) ∈ apTuple k d := by
      refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le hjlt hpk), rfl⟩
    have := hr _ hmem
    apply this
    push_cast
    rw [hj, ZMod.natCast_val, ZMod.cast_id]
    field_simp
  · intro hdvd p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      intro h hh
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hh
      have hzero : (((j : ℤ) * d : ℤ) : ZMod p) = 0 := by
        have : ((p : ℤ)) ∣ ((j : ℤ) * d) := Dvd.dvd.mul_left (hdvd p hp hpk) _
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr this
      rw [hzero]
      exact zero_ne_one
    · exact exists_residue_notMem_of_card_lt hp
        (lt_of_le_of_lt (card_apTuple_le k d) (by omega))

/-- The primorial `n#`: the product of all primes `≤ n`. -/
def primorialUpTo (n : ℕ) : ℕ := ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p

lemma dvd_primorialUpTo {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∣ primorialUpTo n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

lemma not_dvd_primorialUpTo {p n : ℕ} (hp : p.Prime) (hpn : n < p) : ¬ p ∣ primorialUpTo n := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
  obtain ⟨hqr, hqp⟩ := Finset.mem_filter.mp hq
  have : p = q := ((Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq)
  have := Finset.mem_range.mp hqr
  omega

/-- **New admissible gap ranges, `90 ≤ k ≤ 98`.**  For every length `k` in the range
`90 ≤ k ≤ 98`, the arithmetic progression tuple `{0, d, 2d, …, (k-1)d}` with common difference
the primorial `98#` is admissible; moreover, for such `k` a difference `d` yields an admissible
tuple exactly when every prime `p ≤ k` divides `d`, and the smaller primorial `89#` works
precisely for `k ≤ 96`. -/
theorem SingularSeriesGaps9098 :
    (∀ k : ℕ, 90 ≤ k → k ≤ 98 → Admissible (apTuple k (primorialUpTo 98 : ℤ))) ∧
    (∀ k : ℕ, ∀ d : ℤ, 90 ≤ k → k ≤ 98 →
      (Admissible (apTuple k d) ↔ ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d)) ∧
    (∀ k : ℕ, 90 ≤ k → k ≤ 96 → Admissible (apTuple k (primorialUpTo 89 : ℤ))) ∧
    (∀ k : ℕ, 97 ≤ k → k ≤ 98 → ¬ Admissible (apTuple k (primorialUpTo 89 : ℤ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k _ hk98
    refine (admissible_apTuple_iff k _).mpr ?_
    intro p hp hpk
    exact_mod_cast Int.natCast_dvd_natCast.mpr (dvd_primorialUpTo hp (by omega))
  · intro k d _ _
    exact admissible_apTuple_iff k d
  · intro k _ hk96
    refine (admissible_apTuple_iff k _).mpr ?_
    intro p hp hpk
    have hp96 : p ≤ 96 := le_trans hpk hk96
    have hp89 : p ≤ 89 := by
      by_contra hcon
      push_neg at hcon
      -- there is no prime strictly between 89 and 97
      interval_cases p <;> revert hp <;> decide
    exact_mod_cast Int.natCast_dvd_natCast.mpr (dvd_primorialUpTo hp hp89)
  · intro k hk97 _ hadm
    have h97 : ((97 : ℕ) : ℤ) ∣ (primorialUpTo 89 : ℤ) :=
      (admissible_apTuple_iff k _).mp hadm 97 (by norm_num) (by omega)
    exact not_dvd_primorialUpTo (p := 97) (n := 89) (by norm_num) (by norm_num)
      (Int.natCast_dvd_natCast.mp h97)

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

