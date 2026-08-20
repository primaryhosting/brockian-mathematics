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

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma advFn_isSimon {S : Finset (Vec n)} {s : Vec n} (hs : s ≠ 0)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ s) : IsSimon s (advFn S s) := by
  classical
  have hne : ∀ x : Vec n, x ≠ x + s := by
    intro x e
    apply hs
    have h5 : x + x = s := vec_eq_iff_add.mpr e
    rw [vec_add_self] at h5
    exact h5.symm
  have hnotboth : ∀ x : Vec n, x ∈ S → x + s ∉ S := by
    intro x hx hxs
    exact hS x hx (x + s) hxs (hne x) (by rw [← add_assoc, vec_add_self, zero_add])
  set rep : Vec n → Vec n := fun x => if enc x ≤ enc (x + s) then x else x + s with hrep
  have hrep_mem : ∀ x : Vec n, rep x = x ∨ rep x = x + s := by
    intro x; by_cases hc : enc x ≤ enc (x + s) <;> simp [hrep, hc]
  have hrep_shift : ∀ x : Vec n, rep (x + s) = rep x := by
    intro x
    have hxx : enc x ≠ enc (x + s) := fun e => hne x (enc_injective e)
    have hxx' : enc x < enc (x + s) ∨ enc (x + s) < enc x := by omega
    by_cases hc : enc x ≤ enc (x + s)
    · have hc' : ¬ enc (x + s) ≤ enc x := by omega
      simp [hrep, hc, hc', vec_add_add_cancel]
    · have hc' : enc (x + s) ≤ enc x := by omega
      simp [hrep, hc, hc', vec_add_add_cancel]
  have hsmall : ∀ x : Vec n, (x ∈ S ∨ x + s ∈ S) →
      ∃ w ∈ S, (w = x ∨ w = x + s) ∧ advFn S s x = enc w := by
    intro x hx
    by_cases h1 : x ∈ S
    · exact ⟨x, h1, Or.inl rfl, by simp [advFn, h1]⟩
    · have h2 : x + s ∈ S := hx.resolve_left h1
      exact ⟨x + s, h2, Or.inr rfl, by simp [advFn, h1, h2]⟩
  have hbig : ∀ x : Vec n, x ∉ S → x + s ∉ S →
      advFn S s x = Fintype.card (Vec n) + enc (rep x) := by
    intro x h1 h2; simp [advFn, h1, h2, hrep]
  have hfin : ∀ a b : Vec n, (a = b ∨ a = b + s) → (a = b ∨ a + b = s) := by
    intro a b hab
    rcases hab with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [add_comm]; exact vec_eq_iff_add.mpr h)
  refine ⟨hs, ?_⟩
  intro x y
  constructor
  · intro hxy
    refine hfin x y ?_
    by_cases hx : x ∈ S ∨ x + s ∈ S
    · obtain ⟨w, _, hw, hwv⟩ := hsmall x hx
      by_cases hy : y ∈ S ∨ y + s ∈ S
      · obtain ⟨w', _, hw', hw'v⟩ := hsmall y hy
        have hww : w = w' := enc_injective (by rw [← hwv, ← hw'v, hxy])
        subst hww
        rcases hw with h1 | h1 <;> rcases hw' with h2 | h2
        · exact Or.inl (h1 ▸ h2)
        · exact Or.inr (h1 ▸ h2)
        · exact Or.inr (vec_shift (h1 ▸ h2))
        · exact Or.inl (add_right_cancel (h1 ▸ h2 : x + s = y + s))
      · push_neg at hy
        have hyv := hbig y hy.1 hy.2
        rw [hwv, hyv] at hxy
        exact absurd hxy (by have := enc_lt w; omega)
    · push_neg at hx
      have hxv := hbig x hx.1 hx.2
      by_cases hy : y ∈ S ∨ y + s ∈ S
      · obtain ⟨w', _, _, hw'v⟩ := hsmall y hy
        rw [hxv, hw'v] at hxy
        exact absurd hxy (by have := enc_lt w'; omega)
      · push_neg at hy
        have hyv := hbig y hy.1 hy.2
        rw [hxv, hyv] at hxy
        have hrr : rep x = rep y := enc_injective (by omega)
        rcases hrep_mem x with h1 | h1 <;> rcases hrep_mem y with h2 | h2
        · exact Or.inl (by rw [← h1, hrr, h2])
        · exact Or.inr (by rw [← h1, hrr, h2])
        · exact Or.inr (vec_shift (by rw [← h1, hrr, h2]))
        · exact Or.inl (add_right_cancel (by rw [← h1, hrr, h2] : x + s = y + s))
  · intro hxy
    rcases hxy with rfl | hxy
    · rfl
    · have hy : y = x + s := vec_eq_iff_add.mp hxy
      subst hy
      by_cases h1 : x ∈ S
      · have h2 : x + s ∉ S := hnotboth x h1
        have h3 : x + s + s ∈ S := by rwa [vec_add_add_cancel]
        simp [advFn, h1, h2, vec_add_add_cancel]
      · by_cases h2 : x + s ∈ S
        · simp [advFn, h1, h2]
        · have h3 : x + s + s ∉ S := by rwa [vec_add_add_cancel]
          rw [hbig (x + s) h2 h3, hbig x h1 h2, hrep_shift x]

/-! ### The classical lower bound -/

