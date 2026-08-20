import Mathlib

set_option maxHeartbeats 200000

example (r : ZMod 2) (h0 : (0 : ZMod 2) ≠ r) (h1 : (1 : ZMod 2) ≠ r) : False := by
  fin_cases r <;> simp_all

example : ({2, 5, 29} : Finset ℕ).erase 2 = {5, 29} := by
  rw [Finset.erase_insert (by simp)]

example : (∏ p ∈ ({5, 29} : Finset ℕ), (((p : ℚ) - 1) / ((p : ℚ) - 2))) = 112 / 81 := by
  rw [Finset.prod_insert (by simp), Finset.prod_singleton]
  norm_num

example (g : ℕ) (hmod : g % 2 = 1) : (((g : ℤ)) : ZMod 2) = 1 := by
  push_cast
  rw [← ZMod.natCast_mod g 2, hmod]
  norm_num

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of Hardy–Littlewood
prime constellations) if for every prime `p` the reductions of the elements of `H`
mod `p` do not cover all residue classes mod `p`. -/

theorem isAdmissibleGap_iff_even (g : ℕ) : IsAdmissibleGap g ↔ Even g := by
  constructor
  · intro h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hmod : g % 2 = 1 := Nat.odd_iff.mp hodd
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (Finset.mem_insert_self _ _)
    have hg : (((g : ℤ)) : ZMod 2) ≠ r := hr (g : ℤ) (by simp)
    have hgv : (((g : ℤ)) : ZMod 2) = 1 := by
      push_cast
      rw [← ZMod.natCast_mod g 2, hmod]
      norm_num
    rw [hgv] at hg
    simp only [Int.cast_zero] at h0
    fin_cases r <;> simp_all
  · intro heven p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · refine ⟨1, ?_⟩
      intro x hx
      have hmod : g % 2 = 0 := Nat.even_iff.mp heven
      have hgv : (((g : ℤ)) : ZMod 2) = 0 := by
        push_cast
        rw [← ZMod.natCast_mod g 2, hmod]
        norm_num
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using (by decide : (0 : ZMod 2) ≠ 1)
      · rw [hgv]; decide
    · refine admissible_at_of_card_lt hp ?_
      have hcard : ({0, (g : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have : 3 ≤ p := by
        have := hp.two_le
        omega
      omega

/-- Every factor of the singular series is at least one, hence so is the product. -/
