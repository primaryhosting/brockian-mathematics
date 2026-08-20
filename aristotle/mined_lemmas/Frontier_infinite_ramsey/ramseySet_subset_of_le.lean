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

theorem ramseySet_subset_of_le {m n : ℕ} (h : m ≤ n) : ramseySet c n ⊆ ramseySet c m := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.le_zero.1 h
    subst hm
    exact subset_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact (ramseySet_succ_subset c n).trans (ih (Nat.lt_succ_iff.1 hlt))
    · have : m = n + 1 := le_antisymm h hge
      subst this
      exact subset_refl _

