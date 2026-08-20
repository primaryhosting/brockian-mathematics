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

lemma dd_one_apply (G : Type) [Group G] (f : (Fin 1 → G) → ZMod 2) (g : Fin 2 → G) :
    dd G 1 f g = f (fun _ => g 1) + (f (fun _ => g 0 * g 1) + f (fun _ => g 0)) := by
  rw [dd_apply, Fin.sum_univ_two]
  have h0 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have h1 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := by
    funext k; rw [Subsingleton.elim k 0]; simp [Fin.contractNth]
  have h2 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := by
    funext k; rw [Subsingleton.elim k 0]; simp [Fin.contractNth]
  rw [h0, h1, h2]

/-- The `ℤ/2`-vector space of continuous homomorphisms `Gal(F^sep/F) → ℤ/2`. -/
