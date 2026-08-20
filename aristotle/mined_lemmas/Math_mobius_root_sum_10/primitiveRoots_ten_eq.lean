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

namespace Math

open Complex ArithmeticFunction

/-- The Möbius function at `10` equals `1`. -/

lemma primitiveRoots_ten_eq {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    primitiveRoots 10 ℂ = {ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} := by
  have hd : ∀ i j : ℕ, i < 10 → j < 10 → i ≠ j → ζ ^ i ≠ ζ ^ j := by
    intro i j hi hj hij e
    exact hij (h.pow_inj hi hj e)
  have hsub : ({ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.pow_of_coprime 1 (by norm_num)
    · exact h.pow_of_coprime 3 (by decide)
    · exact h.pow_of_coprime 7 (by decide)
    · exact h.pow_of_coprime 9 (by decide)
  have hcard : ({ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hd 1 3 (by norm_num) (by norm_num) (by norm_num),
          hd 1 7 (by norm_num) (by norm_num) (by norm_num),
          hd 1 9 (by norm_num) (by norm_num) (by norm_num)⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hd 3 7 (by norm_num) (by norm_num) (by norm_num),
          hd 3 9 (by norm_num) (by norm_num) (by norm_num)⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hd 7 9 (by norm_num) (by norm_num) (by norm_num)),
      Finset.card_singleton]
  have hc : (primitiveRoots 10 ℂ).card = 4 := by
    rw [Complex.card_primitiveRoots]
    decide
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hc])).symm

/-- **The sum of the primitive 10-th roots of unity equals `μ(10)`.** -/
