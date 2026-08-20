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

namespace CS

variable {α : Type*}

/-- Merge two lists with respect to a boolean comparison `le`. -/

theorem merge_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b ∨ le b a) (xs ys : List α)
    (hx : xs.Pairwise (fun a b => le a b = true))
    (hy : ys.Pairwise (fun a b => le a b = true)) :
    (merge le xs ys).Pairwise (fun a b => le a b = true) := by
  induction xs, ys using CS.merge.induct (le := le) with
  | case1 ys => simpa [merge] using hy
  | case2 xs h => simpa [merge] using hx
  | case3 x xs y ys h ih =>
      rw [List.pairwise_cons] at hx
      rw [merge]; simp only [h, if_true, List.pairwise_cons]
      refine ⟨?_, ih hx.2 hy⟩
      intro a ha
      rcases mem_merge.1 ha with ha | ha
      · exact hx.1 a ha
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact h
        · exact trans _ _ _ h ((List.pairwise_cons.1 hy).1 a ha)
  | case4 x xs y ys h ih =>
      have hyx : le y x = true := by
        rcases total x y with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.pairwise_cons] at hy
      rw [merge]; simp only [h, if_false, Bool.false_eq_true, List.pairwise_cons]
      refine ⟨?_, ih hx hy.2⟩
      intro a ha
      rcases mem_merge.1 ha with ha | ha
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact hyx
        · exact trans _ _ _ hyx ((List.pairwise_cons.1 hx).1 a ha)
      · exact hy.1 a ha

/-- `msort` returns a permutation of its input. -/
