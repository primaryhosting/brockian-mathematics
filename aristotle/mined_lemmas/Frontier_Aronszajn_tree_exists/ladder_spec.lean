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


theorem ladder_spec {α : Ordinal.{0}} (hα : α < ω₁) (hl : Order.IsSuccLimit α) :
    LadderSpec α (ladder α) := by
  have h := exists_ladder hα hl
  rw [ladder, dif_pos h]
  exact h.choose_spec

/-! ### The coherent sequence -/

/-- The coherent sequence of finite-to-one functions: `E α` is a function `Ordinal → ℕ` which
vanishes outside `α`, is finite-to-one on `α`, and agrees with `E β` on `β` up to a finite set,
for every `β < α`. -/
