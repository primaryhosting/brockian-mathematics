import Mathlib

/-!
# Preference relations for Arrow's impossibility theorem

`Pref A` is a weak preference relation on the set of alternatives `A`: a total preorder,
where `r.le a b` means "`b` is at least as good as `a`" (higher is better).

`LinPref A` is a *ranking*: a weak preference with no ties (an antisymmetric total preorder,
i.e. a linear order).

This file develops the basic API together with the constructions of rankings that are used
in the proof of Arrow's theorem.
-/

open scoped Classical

namespace Frontier

/-- A weak preference relation on `A`: a total preorder.
`r.le a b` means "`b` is at least as good as `a`". -/
structure Pref (A : Type*) where
  /-- `le a b` means "`b` is at least as good as `a`". -/
  le : A → A → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c : A}, le a b → le b c → le a c
  le_total : ∀ a b, le a b ∨ le b a

/-- A ranking of the alternatives: a weak preference with no ties. -/
structure LinPref (A : Type*) extends Pref A where
  le_antisymm : ∀ {a b : A}, le a b → le b a → a = b

namespace Pref

variable {A : Type*} (r : Pref A)

/-- Strict preference: `r.lt a b` means "`b` is strictly better than `a`". -/

theorem midPref_lt_bot (r : LinPref A) {b a c : A} (hcb : c ≠ b) (h : r.lt c a) :
    (r.midPref b a).lt c b := by
  have hac : ¬ r.le a c := h
  refine lex_lt.mpr (Or.inl ?_)
  simp [hcb, hac]

end LinPref

end Frontier

import Mathlib
import RequestProject.Basic
import RequestProject.Arrow

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

import RequestProject.Basic

/-!
# Arrow's impossibility theorem

A *social welfare function* `F : SWF V A` aggregates, for each profile of individual rankings
of the alternatives `A` (one ranking `P i : LinPref A` per voter `i : V`), a social weak
preference `F P : Pref A`.

We prove: if there are at least three alternatives and finitely many (at least one) voters, then
no social welfare function satisfies unanimity (Pareto), independence of irrelevant alternatives
and non-dictatorship.
-/

open scoped Classical

namespace Frontier

variable {V A : Type*}

/-- A social welfare function: it maps every profile of individual rankings (strict linear
preferences, i.e. the unrestricted domain) to a social weak preference. -/
