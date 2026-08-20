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
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (le : T → T → Prop) (lvl : T → Ordinal.{0}),
      -- `le` is a partial order
      (∀ x, le x x) ∧
      (∀ x y z, le x y → le y z → le x z) ∧
      (∀ x y, le x y → le y x → x = y) ∧
      -- the predecessors of a node are linearly ordered
      (∀ x y z, le y x → le z x → le y z ∨ le z y) ∧
      -- `lvl` is an order isomorphism from the predecessors of `x` onto `Iio (lvl x)`
      (∀ x y, le y x → y ≠ x → lvl y < lvl x) ∧
      (∀ (x : T) (b : Ordinal.{0}), b < lvl x → ∃! y, le y x ∧ lvl y = b) ∧
      -- the tree has height `ω₁`
      (∀ x, lvl x < ω₁) ∧
      (∀ b < ω₁, ∃ x, lvl x = b) ∧
      -- all levels are countable
      (∀ b : Ordinal.{0}, {x | lvl x = b}.Countable) ∧
      -- all chains are countable
      (∀ C : Set T, (∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x) → C.Countable) := by
  refine ⟨Aronszajn.TreeNode, Aronszajn.tle, Aronszajn.tlvl, Aronszajn.tle_refl,
    fun _ _ _ => Aronszajn.tle_trans, fun _ _ => Aronszajn.tle_antisymm,
    fun _ _ _ => Aronszajn.tle_total_of_le, ?_, fun x b hb => Aronszajn.exists_unique_pred x hb,
    Aronszajn.tlvl_lt_omega1, fun b hb => Aronszajn.exists_node_of_lt hb,
    Aronszajn.countable_level, Aronszajn.countable_chain⟩
  intro x y hyx hne
  rcases lt_or_eq_of_le hyx.1 with h | h
  · exact h
  · exact absurd (Aronszajn.eq_of_tle_of_lvl_eq hyx h) hne

end Frontier

