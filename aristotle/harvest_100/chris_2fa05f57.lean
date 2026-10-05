/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently (by the Euler-product formula for
the singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`), the singular series attached
to `H` is non-zero, so that the Hardy–Littlewood prime `k`-tuple conjecture predicts infinitely
many translates of `H` consisting entirely of primes. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The candidate gap range: the `4`-tuple spanning the interval `[1602, 1610]`. -/
def gapTuple16021610 : Finset ℤ := {1602, 1604, 1608, 1610}

/-- If a prime `p` exceeds the size of `H`, then `H` cannot meet every residue class mod `p`. -/
theorem exists_missed_class_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨by omega⟩
  have hcard : (H.image (fun h : ℤ => (h : ZMod p))).card < p :=
    lt_of_le_of_lt Finset.card_image_le hp
  have hex : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) :=
      fun r _ => hcon r
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at h2
    omega
  obtain ⟨r, hr⟩ := hex
  exact ⟨r, fun h hh hcontra => hr (Finset.mem_image.2 ⟨h, hh, hcontra⟩)⟩

/-- `resCount H p = ν_p(H)` is the number of residue classes modulo `p` occupied by `H`; it is
the local factor entering the singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`. -/
def resCount (H : Finset ℤ) (p : ℕ) : ℕ := (H.image (fun h : ℤ => (h : ZMod p))).card

/-- Admissibility is exactly the statement that every local factor `1 - ν_p(H)/p` of the
singular series is non-zero, i.e. `ν_p(H) < p` for all primes `p`. -/
theorem admissible_iff_resCount_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → resCount H p < p := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : H.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.2 fun hEq => ?_
      have : r ∈ H.image (fun h : ℤ => (h : ZMod p)) := hEq ▸ Finset.mem_univ r
      obtain ⟨h, hh, hhr⟩ := Finset.mem_image.1 this
      exact hr h hh hhr
    have := Finset.card_lt_card hsub
    rwa [Finset.card_univ, ZMod.card] at this
  · intro hH p hp
    have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < p := hH p hp
    have hex : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
      haveI : NeZero p := ⟨hp.ne_zero⟩
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) :=
        fun r _ => hcon r
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_univ, ZMod.card] at h2
      omega
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, fun h hh hcontra => hr (Finset.mem_image.2 ⟨h, hh, hcontra⟩)⟩

/-- The tuple has exactly four elements. -/
theorem card_gapTuple16021610 : gapTuple16021610.card = 4 := by decide

/-- The small local densities of the gap range: the tuple occupies a single class mod `2`,
two classes mod `3`, and four classes mod `5` and mod `7`. -/
theorem resCount_gapTuple16021610 :
    resCount gapTuple16021610 2 = 1 ∧ resCount gapTuple16021610 3 = 2 ∧
      resCount gapTuple16021610 5 = 4 ∧ resCount gapTuple16021610 7 = 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Modulo `2` the only class a set containing `1602` can miss is `1`. -/
theorem missed_class_two (r : ZMod 2) (h : ((1602 : ℤ) : ZMod 2) ≠ r) : r = 1 := by
  revert h; revert r; decide

/-- Modulo `3` the only class a set containing `1602` and `1610` can miss is `1`. -/
theorem missed_class_three (r : ZMod 3) (ha : ((1602 : ℤ) : ZMod 3) ≠ r)
    (hb : ((1610 : ℤ) : ZMod 3) ≠ r) : r = 1 := by
  revert ha hb; revert r; decide

/-- Optimality of the gap range: *any* admissible set contained in the interval `[1602, 1610]`
and containing both endpoints is a subset of `{1602, 1604, 1608, 1610}`.  Indeed the prime `2`
forces all elements to be even, and the prime `3` forces all elements to avoid the class
`1 mod 3`, which rules out `1606`. -/
theorem subset_gapTuple_of_admissible (H : Finset ℤ) (hsub : H ⊆ Finset.Icc (1602 : ℤ) 1610)
    (hadm : Admissible H) (hlo : (1602 : ℤ) ∈ H) (hhi : (1610 : ℤ) ∈ H) :
    H ⊆ gapTuple16021610 := by
  obtain ⟨r2, hr2⟩ := hadm 2 (by norm_num)
  obtain ⟨r3, hr3⟩ := hadm 3 (by norm_num)
  have e2 : r2 = 1 := missed_class_two r2 (hr2 1602 hlo)
  have e3 : r3 = 1 := missed_class_three r3 (hr3 1602 hlo) (hr3 1610 hhi)
  subst e2; subst e3
  intro h hh
  have hA := hr2 h hh
  have hB := hr3 h hh
  have hmem := Finset.mem_Icc.1 (hsub hh)
  obtain ⟨hl, hu⟩ := hmem
  interval_cases h <;> revert hA hB <;> decide

/-- Consequently the gap range admits no admissible configuration of more than four elements
spanning `[1602, 1610]`. -/
theorem card_le_four_of_admissible (H : Finset ℤ) (hsub : H ⊆ Finset.Icc (1602 : ℤ) 1610)
    (hadm : Admissible H) (hlo : (1602 : ℤ) ∈ H) (hhi : (1610 : ℤ) ∈ H) :
    H.card ≤ 4 := by
  have := Finset.card_le_card (subset_gapTuple_of_admissible H hsub hadm hlo hhi)
  rwa [card_gapTuple16021610] at this

/-- **Singular Series Gaps 16021610.**  The `4`-tuple `{1602, 1604, 1608, 1610}` is admissible:
no prime `p` has all of its residue classes covered by the tuple (so its singular series is
non-zero).  Moreover the tuple lies in, and spans, the gap range `[1602, 1610]`, exhibiting an
admissible prime constellation of diameter `8`, and it is the largest such configuration: every
admissible subset of `[1602, 1610]` containing both endpoints is contained in it. -/
theorem SingularSeriesGaps16021610 :
    Admissible gapTuple16021610 ∧
      (∀ h ∈ gapTuple16021610, 1602 ≤ h ∧ h ≤ 1610) ∧
      (1602 : ℤ) ∈ gapTuple16021610 ∧ (1610 : ℤ) ∈ gapTuple16021610 ∧
      (∀ H : Finset ℤ, H ⊆ Finset.Icc (1602 : ℤ) 1610 → Admissible H →
        (1602 : ℤ) ∈ H → (1610 : ℤ) ∈ H → H ⊆ gapTuple16021610) := by
  refine ⟨?_, by decide, by decide, by decide, subset_gapTuple_of_admissible⟩
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact ⟨1, by decide⟩
  by_cases h3 : p = 3
  · subst h3
    exact ⟨1, by decide⟩
  · -- every other prime is at least `5`, which exceeds the size `4` of the tuple
    have hp2 := hp.two_le
    have h5 : 4 < p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · revert hp h2 h3; interval_cases p <;> decide
      · omega
    exact exists_missed_class_of_card_lt _ p (by rw [card_gapTuple16021610]; exact h5)

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

