import Mathlib

/-!
# Singular Series Gaps 13501360 — `ZMod`/Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps13501360.lean`.  The target file there is stated
with elementary `Int` arithmetic (it must begin with a fixed header comment, which precludes an
`import` line); here the same mathematics is recorded in the idiomatic Mathlib language of
`Finset ℤ` and `ZMod p`.
-/

namespace Brockian

/-- A finite set of integers misses a residue class modulo `p`. -/
def AdmissibleAtZMod (H : Finset ℤ) (p : ℕ) : Prop :=
  ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- A finite set of integers is admissible (Hardy–Littlewood prime tuples): for every prime `p`
its reductions modulo `p` do not cover all of `ZMod p`.  This is equivalent to non-vanishing of
the singular series `𝔖(H)`. -/
def AdmissibleZMod (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → AdmissibleAtZMod H p

/-- If `H` has fewer than `p` elements, its reductions cannot cover all `p` residues mod `p`. -/
theorem admissibleAtZMod_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : 0 < p) (hcard : H.card < p) :
    AdmissibleAtZMod H p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < Finset.univ.card (α := ZMod p) := by
    have h1 : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
    have h2 : Finset.univ.card (α := ZMod p) = p := by simp [ZMod.card]
    omega
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨r, fun h hh hcon => hr (Finset.mem_image.2 ⟨h, hh, hcon⟩)⟩

theorem admissibleZMod_pair_of_even {h : ℤ} (hh : Even h) : AdmissibleZMod {0, h} := by
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hval : ((h : ℤ) : ZMod 2) = 0 := by
      obtain ⟨k, hk⟩ := hh
      have : ((h : ℤ) : ZMod 2) = (k : ZMod 2) + (k : ZMod 2) := by
        rw [hk]; push_cast; ring
      rw [this]
      have : (k : ZMod 2) + (k : ZMod 2) = 2 * (k : ZMod 2) := by ring
      rw [this]
      simp [show (2 : ZMod 2) = 0 from rfl]
    rcases hx with rfl | rfl
    · simp
    · rw [hval]; decide
  · refine admissibleAtZMod_of_card_lt hp.pos ?_
    have hcard : ({0, h} : Finset ℤ).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have h2 := hp.two_le
    omega

theorem not_admissibleZMod_pair_of_odd {h : ℤ} (hh : Odd h) : ¬ AdmissibleZMod {0, h} := by
  intro hadm
  obtain ⟨r, hr⟩ := hadm 2 Nat.prime_two
  have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
  have h1 : ((h : ℤ) : ZMod 2) ≠ r := hr h (by simp)
  have hval : ((h : ℤ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hh
    have : ((h : ℤ) : ZMod 2) = (k : ZMod 2) + (k : ZMod 2) + 1 := by
      rw [hk]; push_cast; ring
    rw [this]
    have : (k : ZMod 2) + (k : ZMod 2) = 2 * (k : ZMod 2) := by ring
    rw [this]
    simp [show (2 : ZMod 2) = 0 from rfl]
  rw [hval] at h1
  simp only [Int.cast_zero] at h0
  have : r = 0 ∨ r = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) r
  rcases this with rfl | rfl
  · exact h0 rfl
  · exact h1 rfl

/-- Mathlib/`ZMod` version of the target: for `1350 ≤ h ≤ 1360`, the gap pair `{0, h}` is
admissible iff `h` is even. -/
theorem singularSeriesGaps13501360_zmod :
    ∀ h ∈ Finset.Icc (1350 : ℤ) 1360, (AdmissibleZMod {0, h} ↔ Even h) := by
  intro h _
  refine ⟨fun hadm => ?_, admissibleZMod_pair_of_even⟩
  rcases Int.even_or_odd h with he | ho
  · exact he
  · exact absurd hadm (not_admissibleZMod_pair_of_odd ho)

end Brockian

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The usual notion of a prime natural number: `2 ≤ p` and the only divisors of `p` are `1`
and `p`. -/
def NatPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- `H` misses a residue class modulo `p`: there is some `r` with `0 ≤ r < p` which is not hit by
the reduction modulo `p` of any member of `H`. -/
def AdmissibleAt (H : List Int) (p : Nat) : Prop :=
  ∃ r : Int, 0 ≤ r ∧ r < (p : Int) ∧ ∀ h ∈ H, h % (p : Int) ≠ r

/-- A tuple of integers is *admissible* in the sense of the Hardy–Littlewood prime `k`-tuples
conjecture if, for every prime `p`, its reductions modulo `p` do not cover all residue classes.
This is exactly the condition under which the associated singular series `𝔖(H)` is nonzero. -/
def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, NatPrime p → AdmissibleAt H p

/-- A gap pair `{0, h}` with `h` even is admissible: modulo `2` both entries are `≡ 0`, and modulo
any prime `p ≥ 3` the two entries cannot cover the three residues `0, 1, 2`. -/
theorem admissible_pair_of_even {h : Int} (hh : h % 2 = 0) : Admissible [0, h] := by
  intro p hp
  have hp2 : 2 ≤ p := hp.1
  by_cases hne : p = 2
  · subst hne
    refine ⟨1, by omega, by omega, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · have hp3 : 3 ≤ (p : Int) := by omega
    have hz : (0 : Int) % (p : Int) = 0 := Int.zero_emod _
    by_cases hc : h % (p : Int) = 1
    · refine ⟨2, by omega, by omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hz]; decide
      · rw [hc]; decide
    · refine ⟨1, by omega, by omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hz]; decide
      · exact hc

/-- A gap pair `{0, h}` with `h` odd is never admissible: modulo `2` the two entries already
cover both residue classes, so the singular series vanishes. -/
theorem not_admissible_pair_of_odd {h : Int} (hh : h % 2 = 1) : ¬ Admissible [0, h] := by
  intro hadm
  obtain ⟨r, hr0, hr1, hr⟩ := hadm 2 ⟨by omega, by
    intro m hm
    have h2 : m ≤ 2 := Nat.le_of_dvd (by decide) hm
    have h0 : m ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hm) (by decide)
    have : m ≠ 0 ∧ m ≤ 2 := ⟨h0, h2⟩
    rcases Nat.lt_or_ge m 2 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)⟩
  have h0 : (0 : Int) % ((2 : Nat) : Int) ≠ r := hr 0 (by simp)
  have h1 : h % ((2 : Nat) : Int) ≠ r := hr h (by simp)
  omega

/-- **Singular series gaps in the range `[1350, 1360]`.**

For every integer `h` with `1350 ≤ h ≤ 1360`, the gap pair `{0, h}` is an admissible tuple —
equivalently, its Hardy–Littlewood singular series is nonzero — exactly when `h` is even.
This extends the `SingularSeriesGaps` family with the admissible gap range `[1350, 1360]`. -/
theorem SingularSeriesGaps13501360 :
    ∀ h : Int, 1350 ≤ h → h ≤ 1360 → (Admissible [0, h] ↔ h % 2 = 0) := by
  intro h _ _
  refine ⟨fun hadm => ?_, admissible_pair_of_even⟩
  have hcases : h % 2 = 0 ∨ h % 2 = 1 := by omega
  rcases hcases with h0 | h1
  · exact h0
  · exact absurd hadm (not_admissible_pair_of_odd h1)

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

