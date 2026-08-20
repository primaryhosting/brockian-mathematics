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

noncomputable def milnorK2OneEquiv : MilnorK2 F 1 ≃ₗ[ZMod 2] SquareClasses F :=
  LinearEquiv.ofLinear (milnorK2OneToSquareClasses F) (squareClassesToMilnorK2One F)
    (by
      refine LinearMap.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H a =>
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        show milnorK2OneToSquareClasses F
            (squareClassesToMilnorK2One F (Additive.ofMul (QuotientGroup.mk a)))
          = Additive.ofMul (QuotientGroup.mk a)
        rw [squareClassesToMilnorK2One_mk, milnorK2OneToSquareClasses_sym1])
    (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | H f =>
        induction f using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
            simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at *
            rw [Submodule.Quotient.mk_add, map_add, map_add, hf, hg]
        | single v c =>
            have hv : (fun _ => v 0) = v := by funext j; rw [Subsingleton.elim j 0]
            have hs : Submodule.Quotient.mk (Finsupp.single v (1 : ZMod 2)) = sym1 F (v 0) := by
              rw [sym1, hv]
            have h1 : Finsupp.single v c = c • Finsupp.single v (1 : ZMod 2) := by
              simp [Finsupp.smul_single]
            simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
            rw [h1, Submodule.Quotient.mk_smul, map_smul, map_smul, hs,
              milnorK2OneToSquareClasses_sym1, squareClassesToMilnorK2One_mk])

end DegreeOne

/-!
## Degree one on the Galois side, and a Lean-checked reduction to Kummer theory

In degree `1` the continuous cochain description makes `H^1(F, ℤ/2)` the group of continuous
homomorphisms `Gal(F^sep/F) → ℤ/2` (there are no coboundaries in degree one, because the
differential out of degree zero vanishes for trivial coefficients).

Combining this with `k^M_1(F) = Fˣ/(Fˣ)²` reduces the degree-one Milnor conjecture to Kummer
theory: `NormResidueIso F 1` holds if and only if `Fˣ/(Fˣ)²` is isomorphic to the group of
continuous homomorphisms `Gal(F^sep/F) → ℤ/2`.
-/

section GaloisDegreeOne

variable (F : Type) [Field F]

