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

noncomputable def contCohomologyOneEquiv : contCohomology G 1 ≃ₗ[ZMod 2] contChars G := by
  have h1 : Submodule.comap (contCocycles G 1).subtype (contCoboundaries G 1) = ⊥ := by
    rw [contCoboundaries_one_eq_bot, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot_of_injective (Submodule.injective_subtype _)
  exact (Submodule.quotEquivOfEqBot _ h1).trans
    (((cochainOneEquiv G).submoduleMap (contCocycles G 1)).trans
      (LinearEquiv.ofEq _ _ (map_contCocycles_one G)))

end Frontier

import Mathlib
import RequestProject.Frontier.ContinuousCohomology
import RequestProject.Frontier.MilnorK

/-!
# The norm residue map in degree one (Kummer theory)

For a field `F` with `char F ≠ 2` we construct the degree-one norm residue map
`K^M_1(F)/2 = Fˣ/(Fˣ)² → H¹(Gal(F^sep/F), ℤ/2)`, `a ↦ (σ ↦ σ(√a)/√a)`, and prove
that it is bijective.  This is the degree-one case of the Milnor conjecture
(Voevodsky's theorem), which in this degree is classical Kummer theory.

## Main definitions

* `Frontier.GalGroup F` : the absolute Galois group `Gal(F^sep/F)`.
* `Frontier.kummerChar a` : the quadratic character `σ ↦ σ(√a)/√a` with values in `ℤ/2`.
* `Frontier.normResidueOne` : the induced map `K^M_1(F)/2 → Homcont(Gal(F^sep/F), ℤ/2)`.

## Main results

* `Frontier.normResidueOne_bijective` : the degree-one norm residue map is bijective.
-/

namespace Frontier

open IntermediateField

attribute [local instance] Classical.propDecidable

variable (F : Type) [Field F]

/-- The absolute Galois group of `F`, i.e. `Gal(F^sep/F)`, with the Krull topology. -/
abbrev GalGroup := SeparableClosure F ≃ₐ[F] SeparableClosure F

variable {F}

/-- A chosen square root in `F^sep` of (the image of) a unit of `F`. -/
