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

lemma map_contCocycles_one :
    Submodule.map (ev1 F).toLinearMap (contCocycles F 1) = contHom1 F := by
  ext u
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (mem_contCocycles_one_iff F f).1 hf
  · intro hu
    refine ⟨(ev1 F).symm u, ?_, by simp⟩
    have h : ev1 F ((ev1 F).symm u) = u := by simp
    exact (mem_contCocycles_one_iff F _).2 (by rw [h]; exact hu)

/-- **Mod-2 Galois cohomology in degree one is the group of continuous homomorphisms
`Gal(F^sep/F) → ℤ/2`.** -/
