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

/-!
# Existence of an Aronszajn tree

An *Aronszajn tree* is a tree of height `ω₁` all of whose levels are countable and which has no
uncountable chain (equivalently, no uncountable branch).

We construct one in the classical way, from a *coherent sequence* of finite-to-one functions
`E α : α → ℕ` (`α < ω₁`), built by transfinite recursion: `E α` is finite-to-one on `α`, and for
`β < α` the functions `E α ↾ β` and `E β` differ at only finitely many places.  The tree consists
of all pairs `(α, f)` with `α < ω₁` and `f : α → ℕ` differing from `E α` at only finitely many
places, ordered by end-extension.
-/

namespace Frontier

open Ordinal Cardinal Set

/-! ### Countability and `ω₁` -/


theorem E_limit_block {α : Ordinal.{0}} (hα : α < ω₁) (hl : Order.IsSuccLimit α)
    {ξ : Ordinal.{0}} (hξ : ξ < α) :
    ∃ m : ℕ, ξ < ladder α (m + 1) ∧ (∀ j : ℕ, ξ < ladder α (j + 1) → m ≤ j) ∧
      E α ξ = max (E (ladder α (m + 1)) ξ) m := by
  obtain ⟨h0, hmono, hlt, hcof⟩ := ladder_spec hα hl
  obtain ⟨n, hn⟩ := hcof ξ hξ
  have hex : ∃ n : ℕ, ξ < ladder α (n + 1) := by
    cases n with
    | zero => rw [h0] at hn; simp at hn
    | succ n => exact ⟨n, hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min' hex hj, ?_⟩
  rw [E_limit hl, if_pos hξ, dif_pos hex, dif_pos (hlt _)]

