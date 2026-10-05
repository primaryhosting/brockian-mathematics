/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem pred_exists (y : Node) (β : Ordinal) (hβ : β < y.len) :
    ∃! x : Node, x < y ∧ x.len = β := by
  refine ⟨y.restr β hβ, ⟨y.restr_lt β hβ, rfl⟩, ?_⟩
  rintro x ⟨hx, hxlen⟩
  refine Node.ext hxlen (funext fun ξ => ?_)
  rcases lt_or_ge ξ β with h | h
  · show x.fn ξ = if ξ < β then y.fn ξ else 0
    rw [if_pos h]
    exact hx.le.2 ξ (hxlen ▸ h)
  · show x.fn ξ = if ξ < β then y.fn ξ else 0
    rw [if_neg (not_lt.mpr h), x.fn_zero ξ (hxlen ▸ h)]

end Node

/-- `IsAronszajnTree T ht` states that the partial order `T`, with level function `ht`, is an
Aronszajn tree: it is a tree (the predecessors of any node form a chain, well ordered by the
level function, with exactly one predecessor at each smaller level), it has height `ω₁`
(every countable ordinal occurs as a level, and no other level occurs), every level is
countable, and there is no uncountable chain (branch). -/
structure IsAronszajnTree (T : Type*) [PartialOrder T] (ht : T → Ordinal.{0}) : Prop where
  /-- Every node lives at a countable level. -/
  ht_lt_omega1 : ∀ x, ht x < ω₁
  /-- The level function is strictly monotone. -/
  ht_strictMono : ∀ ⦃x y : T⦄, x < y → ht x < ht y
  /-- The predecessors of a node form a chain. -/
  pred_linear : ∀ y x x' : T, x < y → x' < y → x ≤ x' ∨ x' ≤ x
  /-- A node of level `α` has exactly one predecessor at each level `β < α`. -/
  pred_exists : ∀ (y : T) (β : Ordinal), β < ht y → ∃! x, x < y ∧ ht x = β
  /-- The tree has height `ω₁`: every countable level is inhabited. -/
  levels_nonempty : ∀ α < ω₁, ∃ x, ht x = α
  /-- Every level is countable. -/
  levels_countable : ∀ α, {x | ht x = α}.Countable
  /-- There is no uncountable branch. -/
  chains_countable : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable

end Aronszajn

open Aronszajn in
/-- **There is an Aronszajn tree**: a tree of height `ω₁` all of whose levels are countable
and which has no uncountable branch. -/
