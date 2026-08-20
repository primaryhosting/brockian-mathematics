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

def milnorRelSet (n : ℕ) : Set ((Fin n → Fˣ) →₀ ZMod 2) :=
  {x | (∃ (i : Fin n) (v : Fin n → Fˣ) (a b : Fˣ),
          x = Finsupp.single (Function.update v i (a * b)) 1
              - Finsupp.single (Function.update v i a) 1
              - Finsupp.single (Function.update v i b) 1) ∨
       (∃ (i : Fin n) (h : (i : ℕ) + 1 < n) (v : Fin n → Fˣ),
          ((v i : F) + (v ⟨(i : ℕ) + 1, h⟩ : F) = 1) ∧ x = Finsupp.single v 1)}

/-- Mod-2 Milnor K-theory `k^M_n(F) = K^M_n(F)/2` of a field `F`, in degree `n`. -/
abbrev MilnorK2 (n : ℕ) : Type :=
  ((Fin n → Fˣ) →₀ ZMod 2) ⧸ Submodule.span (ZMod 2) (milnorRelSet F n)

end Milnor

/-!
## Mod-2 Galois cohomology

`H^n(F, ℤ/2)` is the continuous (i.e. locally constant) cochain cohomology of the absolute
Galois group `Gal(F^sep/F)`, equipped with its Krull topology, acting trivially on `ℤ/2`.

The differential is the usual inhomogeneous cochain differential (borrowed from Mathlib's group
cohomology, for the trivial representation); over `ℤ/2` with trivial action all the signs in it
disappear, so `d f (g₀,…,gₙ)` is the plain sum of the faces.
-/

section GaloisCohomology

open groupCohomology

/-- The absolute Galois group of `F`, with its Krull topology. -/
abbrev AbsGal (F : Type) [Field F] : Type := SeparableClosure F ≃ₐ[F] SeparableClosure F

/-- The inhomogeneous cochain differential with `ℤ/2` coefficients and trivial action. -/
