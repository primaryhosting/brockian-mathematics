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

theorem infinite_ramsey_lt (c : ℕ → ℕ → Bool) :
    ∃ S : Set ℕ, S.Infinite ∧ ∃ b : Bool, ∀ i ∈ S, ∀ j ∈ S, i < j → c i j = b := by
  have hcol : ∃ b : Bool, {n : ℕ | ramseyColor c n = b}.Infinite := by
    by_contra hcon
    push_neg at hcon
    have h1 := hcon true
    have h0 := hcon false
    have : (Set.univ : Set ℕ).Finite := by
      have hsub : (Set.univ : Set ℕ) ⊆
          {n : ℕ | ramseyColor c n = true} ∪ {n : ℕ | ramseyColor c n = false} := by
        intro n _
        rcases Bool.eq_false_or_eq_true (ramseyColor c n) with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact Set.Finite.subset (h1.union h0) hsub
    exact Set.infinite_univ this
  obtain ⟨b, hb⟩ := hcol
  refine ⟨ramseyElt c '' {n : ℕ | ramseyColor c n = b}, ?_, b, ?_⟩
  · exact hb.image ((ramseyElt_strictMono c).injective.injOn)
  · rintro i ⟨m, hm, rfl⟩ j ⟨n, hn, rfl⟩ hlt
    have hmn : m < n := (ramseyElt_strictMono c).lt_iff_lt.1 hlt
    rw [ramseyElt_color c hmn]
    exact hm

end Ramsey

/-- **Infinite Ramsey theorem for pairs**: every `2`-colouring of the unordered pairs
`[ℕ]²` admits an infinite monochromatic set, i.e. an infinite `S ⊆ ℕ` and a colour `b`
such that every pair of distinct elements of `S` has colour `b`. -/
