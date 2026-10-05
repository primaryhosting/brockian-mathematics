/-
/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- A finite set of integers `H` is *admissible* if for every prime `p` the reductions of the
elements of `H` modulo `p` omit at least one residue class.  Equivalently, the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` of the Hardy–Littlewood prime `k`-tuple conjecture
is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- `nu p H` is the number `ν_p(H)` of residue classes modulo `p` occupied by `H`. -/
noncomputable def nu (p : ℕ) (H : Finset ℤ) : ℕ :=
  (H.image (fun h : ℤ => (h : ZMod p))).card

/-- The candidate tuple: the primes in the interval `[251, 1709]`, viewed as integers. -/
def gapTuple : Finset ℤ := ((Finset.Ico 251 1711).filter Nat.Prime).image (fun n : ℕ => (n : ℤ))

/-! ### Cardinality of the tuple -/

private lemma primeCount_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Finset.Ico a c).filter Nat.Prime).card
      = ((Finset.Ico a b).filter Nat.Prime).card
        + ((Finset.Ico b c).filter Nat.Prime).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact (Finset.Ico_disjoint_Ico_consecutive a b c).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private lemma primeCount_Ico_251_1711 : ((Finset.Ico 251 1711).filter Nat.Prime).card = 214 := by
  have c1 : ((Finset.Ico 251 397).filter Nat.Prime).card = 24 := by decide +kernel
  have c2 : ((Finset.Ico 397 543).filter Nat.Prime).card = 23 := by decide +kernel
  have c3 : ((Finset.Ico 543 689).filter Nat.Prime).card = 24 := by decide +kernel
  have c4 : ((Finset.Ico 689 835).filter Nat.Prime).card = 21 := by decide +kernel
  have c5 : ((Finset.Ico 835 981).filter Nat.Prime).card = 20 := by decide +kernel
  have c6 : ((Finset.Ico 981 1127).filter Nat.Prime).card = 23 := by decide +kernel
  have c7 : ((Finset.Ico 1127 1273).filter Nat.Prime).card = 17 := by decide +kernel
  have c8 : ((Finset.Ico 1273 1419).filter Nat.Prime).card = 18 := by decide +kernel
  have c9 : ((Finset.Ico 1419 1565).filter Nat.Prime).card = 23 := by decide +kernel
  have c10 : ((Finset.Ico 1565 1711).filter Nat.Prime).card = 21 := by decide +kernel
  rw [primeCount_split (show (251:ℕ) ≤ 397 by norm_num) (show (397:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (397:ℕ) ≤ 543 by norm_num) (show (543:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (543:ℕ) ≤ 689 by norm_num) (show (689:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (689:ℕ) ≤ 835 by norm_num) (show (835:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (835:ℕ) ≤ 981 by norm_num) (show (981:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (981:ℕ) ≤ 1127 by norm_num) (show (1127:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (1127:ℕ) ≤ 1273 by norm_num) (show (1273:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (1273:ℕ) ≤ 1419 by norm_num) (show (1419:ℕ) ≤ 1711 by norm_num),
    primeCount_split (show (1419:ℕ) ≤ 1565 by norm_num) (show (1565:ℕ) ≤ 1711 by norm_num),
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]

lemma gapTuple_card : gapTuple.card = 214 := by
  rw [gapTuple, Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    primeCount_Ico_251_1711]

/-! ### Membership facts -/

lemma mem_gapTuple_iff {x : ℤ} :
    x ∈ gapTuple ↔ ∃ n : ℕ, n.Prime ∧ 251 ≤ n ∧ n < 1711 ∧ (n : ℤ) = x := by
  simp only [gapTuple, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨n, ⟨⟨h1, h2⟩, hp⟩, rfl⟩; exact ⟨n, hp, h1, h2, rfl⟩
  · rintro ⟨n, hp, h1, h2, rfl⟩; exact ⟨n, ⟨⟨h1, h2⟩, hp⟩, rfl⟩

lemma gapTuple_lower {x : ℤ} (hx : x ∈ gapTuple) : (251 : ℤ) ≤ x := by
  obtain ⟨n, _, h1, _, rfl⟩ := mem_gapTuple_iff.mp hx
  exact_mod_cast h1

lemma gapTuple_upper {x : ℤ} (hx : x ∈ gapTuple) : x ≤ (1709 : ℤ) := by
  obtain ⟨n, hp, _, h2, rfl⟩ := mem_gapTuple_iff.mp hx
  have hne : n ≠ 1710 := by rintro rfl; exact absurd hp (by norm_num)
  have : n ≤ 1709 := by omega
  exact_mod_cast this

lemma mem_gapTuple_251 : (251 : ℤ) ∈ gapTuple :=
  mem_gapTuple_iff.mpr ⟨251, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma mem_gapTuple_1709 : (1709 : ℤ) ∈ gapTuple :=
  mem_gapTuple_iff.mpr ⟨1709, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### Admissibility -/

/-- Pigeonhole: a set with fewer than `p` elements cannot cover all residues mod `p`. -/
lemma exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) [NeZero p] (h : H.card < p) :
    ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hc r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at hcard
  exact absurd (hcard.trans (Finset.card_image_le)) (not_le.mpr h)

/-- For a small prime `p` (at most `250`) the residue class `0` is missed, since every element of
the tuple is a prime larger than `p`. -/
lemma zero_missed_of_small {p : ℕ} (hp : p.Prime) (hle : p ≤ 250) :
    ∀ h ∈ gapTuple, (h : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro x hx
  obtain ⟨n, hn, h1, _, rfl⟩ := mem_gapTuple_iff.mp hx
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq hp hn).mp hdvd
  omega

theorem gapTuple_admissible : Admissible gapTuple := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases le_or_gt p 250 with hle | hgt
  · exact ⟨0, zero_missed_of_small hp hle⟩
  · exact exists_missed_residue_of_card_lt gapTuple p (by rw [gapTuple_card]; omega)

/-- Admissibility expressed through the local densities: for every prime `p` the number
`ν_p(H)` of occupied residue classes is smaller than `p`, i.e. every local factor of the
singular series is positive. -/
theorem gapTuple_nu_lt (p : ℕ) (hp : p.Prime) : nu p gapTuple < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r, hr⟩ := gapTuple_admissible p hp
  have hsub : gapTuple.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    have : r ∈ gapTuple.image (fun h : ℤ => (h : ZMod p)) := by rw [hEq]; exact Finset.mem_univ r
    obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp this
    exact hr x hx hxr
  have := Finset.card_lt_card hsub
  rwa [Finset.card_univ, ZMod.card] at this

/-- **Singular Series Gaps 14501460.**  There is an admissible tuple of `214` integers whose
diameter `1458` lies in the gap range `[1450, 1460]`; consequently every local factor of its
singular series is positive.  (Admissibility of such a tuple is exactly the hypothesis needed for
the Hardy–Littlewood conjecture to predict infinitely many prime constellations with this gap.) -/
theorem SingularSeriesGaps14501460 :
    Admissible gapTuple ∧ gapTuple.card = 214 ∧
      (∀ p : ℕ, p.Prime → nu p gapTuple < p) ∧
      ∃ a ∈ gapTuple, ∃ b ∈ gapTuple,
        (∀ h ∈ gapTuple, a ≤ h ∧ h ≤ b) ∧ 1450 ≤ b - a ∧ b - a ≤ 1460 := by
  refine ⟨gapTuple_admissible, gapTuple_card, gapTuple_nu_lt, 251, mem_gapTuple_251, 1709,
    mem_gapTuple_1709, fun h hh => ⟨gapTuple_lower hh, gapTuple_upper hh⟩, by norm_num, by
      norm_num⟩

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

