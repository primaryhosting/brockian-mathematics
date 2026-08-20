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

lemma normResidueOneChars_bijective (hF : (2 : F) ≠ 0) :
    Function.Bijective (normResidueOneChars hF) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := exists_symbol_eq_one x
    rw [normResidueOneChars_symbol] at hx
    have hchar : (kummerChar a : GalGroup F → ZMod 2) = 0 := congrArg Subtype.val hx
    obtain ⟨b, rfl⟩ := isSquare_of_kummerChar_eq_zero hF a hchar
    exact symbol_one_sq b
  · rintro ⟨chi, hchi⟩
    obtain ⟨a, ha⟩ := exists_kummerChar_eq hF chi hchi
    exact ⟨symbol F (fun _ => a), by rw [normResidueOneChars_symbol]; exact Subtype.ext ha⟩

/-- The degree-one norm residue map `K^M_1(F)/2 → H¹(Gal(F^sep/F), ℤ/2)`. -/
