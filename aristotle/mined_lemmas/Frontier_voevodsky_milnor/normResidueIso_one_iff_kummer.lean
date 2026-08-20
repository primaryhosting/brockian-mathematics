import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/

theorem normResidueIso_one_iff_kummer :
    NormResidueIso F 1 ↔ Nonempty (SquareClasses F ≃ₗ[ZMod 2] contHom1 F) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨((milnorK2OneEquiv F).symm.trans e).trans (galoisCohomologyMod2OneEquiv F)⟩
  · rintro ⟨e⟩
    exact ⟨((milnorK2OneEquiv F).trans e).trans (galoisCohomologyMod2OneEquiv F).symm⟩

end GaloisDegreeOne

end Frontier

import RequestProject.Core

/-!
# Kummer theory in degree one

The degree-one Milnor conjecture is Kummer theory: the square classes `Fˣ/(Fˣ)²` of a field of
characteristic `≠ 2` are the continuous characters `Gal(F^sep/F) → ℤ/2`.

This file constructs the Kummer character of a unit and proves that the resulting map
`Fˣ/(Fˣ)² → H^1(F, ℤ/2)` is a well-defined injective `ℤ/2`-linear map.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace Frontier

section Kummer

variable {F : Type} [Field F]

open scoped Classical in
/-- The Kummer character attached to an element `s` of the separable closure: it records, for each
element of the absolute Galois group, whether `s` is moved. -/
