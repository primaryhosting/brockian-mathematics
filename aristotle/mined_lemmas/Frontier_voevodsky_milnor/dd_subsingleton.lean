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

lemma dd_subsingleton (G : Type) [Group G] [Subsingleton G] (n : ℕ)
    (f : (Fin n → G) → ZMod 2) (g : Fin (n + 1) → G) (g' : Fin n → G) :
    dd G n f g = (n : ZMod 2) * f g' := by
  rw [dd_apply]
  have h : ∀ g'' : Fin n → G, f g'' = f g' := fun g'' => by
    congr 1; exact Subsingleton.elim _ _
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ((n : ZMod 2) + 1 + 1) = (n : ZMod 2) := by
    rw [add_assoc, show ((1 : ZMod 2) + 1) = 0 from rfl, add_zero]
  push_cast
  linear_combination (f g') * h2

variable (F : Type) [Field F]

/-- The submodule of continuous (= locally constant) `n`-cochains. -/
