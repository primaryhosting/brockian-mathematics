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

import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

`K^M_n(F)/2` is the abelian group (a `ZMod 2`-vector space) presented by generators the
symbols `{a₁, …, aₙ}` with `aᵢ ∈ Fˣ`, subject to
* multilinearity `{…, a·b, …} = {…, a, …} + {…, b, …}`, and
* the Steinberg relation `{…, a, …, 1 - a, …} = 0`.

Since the coefficients are taken in `ZMod 2` this is exactly Milnor K-theory modulo `2`.

## Main definitions

* `Frontier.milnorRelations F n` : the set of defining relations.
* `Frontier.KMilnorMod2 F n` : the group `K^M_n(F)/2`.
* `Frontier.symbol F v` : the symbol `{v 0, …, v (n-1)}`.

## Main results

* `Frontier.kMilnorMod2ZeroEquiv` : `K^M_0(F)/2 ≃ ℤ/2`.
* `Frontier.exists_symbol_eq_one` : in degree one, every element is a single symbol.
-/

namespace Frontier

variable (F : Type) [Field F]

/-- The defining relations of `K^M_n(F)/2`: multilinearity in each slot and the Steinberg
relation `{…, a, …, 1 - a, …} = 0`. -/

noncomputable def kMilnorMod2ZeroEquiv : KMilnorMod2 F 0 ≃ₗ[ZMod 2] ZMod 2 := by
  have hrel : milnorRelations F 0 = ∅ := by
    ext x
    simp only [milnorRelations, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro (⟨i, _⟩ | ⟨i, _⟩) <;> exact i.elim0
  have hbot : Submodule.span (ZMod 2) (milnorRelations F 0) = ⊥ := by
    rw [hrel, Submodule.span_empty]
  exact (Submodule.quotEquivOfEqBot _ hbot).trans
    (Finsupp.LinearEquiv.finsuppUnique (ZMod 2) (ZMod 2) (Fin 0 → Fˣ))

variable {F}

/-- Degree-one symbols are multiplicative. -/
