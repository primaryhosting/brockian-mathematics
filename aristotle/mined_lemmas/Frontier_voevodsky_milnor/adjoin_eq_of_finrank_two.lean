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

lemma adjoin_eq_of_finrank_two {L : IntermediateField F (SeparableClosure F)}
    (hL : Module.finrank F L = 2) {y : SeparableClosure F} (hy : y ∈ L)
    (hy' : y ∉ (⊥ : IntermediateField F (SeparableClosure F))) :
    IntermediateField.adjoin F {y} = L := by
  have hfin : FiniteDimensional F L := by
    apply FiniteDimensional.of_finrank_pos (K := F) (V := L)
    rw [hL]
    norm_num
  have hle : IntermediateField.adjoin F {y} ≤ L := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl
    exact hy
  have hfin' : FiniteDimensional F (IntermediateField.adjoin F {y}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  have hne1 : Module.finrank F (IntermediateField.adjoin F {y}) ≠ 1 := by
    intro h
    apply hy'
    have hbot : IntermediateField.adjoin F {y} = ⊥ :=
      IntermediateField.finrank_eq_one_iff.1 h
    have : y ∈ IntermediateField.adjoin F {y} :=
      IntermediateField.subset_adjoin F {y} rfl
    rwa [hbot] at this
  have hpos : 0 < Module.finrank F (IntermediateField.adjoin F {y}) :=
    Module.finrank_pos
  refine IntermediateField.eq_of_le_of_finrank_le hle ?_
  rw [hL]
  omega

