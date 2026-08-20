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

def contHom1 : Submodule (ZMod 2) (AbsGal F → ZMod 2) where
  carrier := {f | IsLocallyConstant f ∧ ∀ g h, f (g * h) = f g + f h}
  add_mem' := fun {f f'} hf hf' =>
    ⟨IsLocallyConstant.comp₂ hf.1 hf'.1 (· + ·), fun g h => by
      simp only [Pi.add_apply, hf.2, hf'.2]; abel⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => by simp⟩
  smul_mem' := fun c f hf =>
    ⟨hf.1.comp (c * ·), fun g h => by simp only [Pi.smul_apply, smul_eq_mul, hf.2]; ring⟩

/-- Degree-one cochains are the same thing as functions on the Galois group. -/
