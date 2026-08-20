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

namespace Frontier

section Ramsey

variable (c : ℕ → ℕ → Bool)

/-- The elements of `A` strictly above `a` receiving colour `b` (paired with `a`). -/

theorem nextSet_infinite {A : Set ℕ} (hA : A.Infinite) : (nextSet c A).Infinite := by
  by_cases h : (branch c A (sInf A) true).Infinite
  · simp [nextSet, nextColor, h]
  · have hsplit : {x ∈ A | sInf A < x} ⊆
        branch c A (sInf A) true ∪ branch c A (sInf A) false := by
      rintro x ⟨hx, hlt⟩
      rcases Bool.eq_false_or_eq_true (c (sInf A) x) with hc | hc
      · exact Or.inl ⟨hx, hlt, hc⟩
      · exact Or.inr ⟨hx, hlt, hc⟩
    have hbig : {x ∈ A | sInf A < x}.Infinite := by
      have : A \ {x | x ≤ sInf A} ⊆ {x ∈ A | sInf A < x} := by
        rintro x ⟨hx, hx2⟩
        exact ⟨hx, lt_of_not_ge (by simpa using hx2)⟩
      refine Set.Infinite.mono this ?_
      exact hA.diff (Set.finite_Iic (sInf A))
    have hunion : (branch c A (sInf A) true ∪ branch c A (sInf A) false).Infinite :=
      hbig.mono hsplit
    have := (Set.infinite_union).1 hunion
    rcases this with h' | h'
    · exact absurd h' h
    · simpa [nextSet, nextColor, h] using h'

