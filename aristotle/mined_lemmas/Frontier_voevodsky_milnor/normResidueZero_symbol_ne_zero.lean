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

lemma normResidueZero_symbol_ne_zero (F : Type) [Field F] (v : Fin 0 → Fˣ) :
    normResidueZero F (symbol F v) ≠ 0 := by
  intro h
  have h1 : symbol F v = 0 := (normResidueZeroEquiv F).map_eq_zero_iff.1 h
  have h2 : kMilnorMod2ZeroEquiv F (symbol F v) = 0 := by
    rw [h1, map_zero]
  have h3 : kMilnorMod2ZeroEquiv F (symbol F v) = 1 := by
    have hs : ∀ w : Fin 0 → Fˣ, (Finsupp.single v (1 : ZMod 2)) w = 1 := by
      intro w
      rw [Subsingleton.elim w v, Finsupp.single_eq_same]
    simp [kMilnorMod2ZeroEquiv, symbol, Submodule.quotEquivOfEqBot,
      Finsupp.LinearEquiv.finsuppUnique, hs]
  rw [h3] at h2
  exact one_ne_zero h2

/-- The Milnor conjecture (Voevodsky's theorem): for a field of characteristic `≠ 2`, mod-2
Milnor K-theory agrees with mod-2 Galois cohomology in every degree.  This is recorded for
reference only, and in a weak form: the isomorphism is asked for merely as an isomorphism of
`ℤ/2`-vector spaces, since writing down the norm residue map in degrees `≥ 2` requires cup
products, which are not developed here.  It is not proved. -/
