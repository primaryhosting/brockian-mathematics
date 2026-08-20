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


theorem E_eq_zero_of_le {α ξ : Ordinal.{0}} (h : α ≤ ξ) : E α ξ = 0 := by
  revert h
  induction α using Ordinal.limitRecOn with
  | zero => intro _; exact E_zero ξ
  | succ β _ =>
      intro h
      rw [E_succ, if_neg (not_lt.mpr (le_trans (Order.le_succ β) h))]
  | limit α hl _ =>
      intro h
      rw [E_limit hl, if_neg (not_lt.mpr h)]

/-- At a countable limit ordinal, every `ξ < α` lies in a block of the ladder, and the value of
`E α` there is computed from the value of `E` at the top of that block. -/
