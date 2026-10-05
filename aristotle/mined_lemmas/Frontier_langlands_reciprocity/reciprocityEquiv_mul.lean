/-
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## The abstract shape of Langlands reciprocity

The Langlands reciprocity conjecture asserts that the "Galois side" of arithmetic
(continuous representations of a Galois group) and the "automorphic side"
(automorphic representations of a reductive group) are in a bijection which matches
*local parameters*: at every unramified place `v` the Frobenius conjugacy class on the
Galois side has the same characteristic data as the Satake parameter of the automorphic
representation. Since matching of local parameters at almost all places determines the
matching of the associated `L`-functions, this is the precise content of "reciprocity".

The following predicate isolates that shape, abstracting away the (currently
unformalisable in full) analytic definitions of automorphic representations: a
*reciprocity law* for a pair of local-parameter maps
`galoisParam : 𝒢 → Place → Param` and `autParam : 𝒜 → Place → Param`
is a bijection `𝒢 ≃ 𝒜` matching the parameters at every place.
-/

/-- **Langlands reciprocity, abstract form.** Given a family of "Galois objects" `𝒢`
and "automorphic objects" `𝒜`, each equipped with local parameters at every place of
`Place` valued in `Param`, reciprocity asserts the existence of a bijection between them
which matches the local parameters at all places. -/

theorem reciprocityEquiv_mul (ρ₁ ρ₂ : GaloisChar N) :
    reciprocityEquiv N (ρ₁ * ρ₂) = reciprocityEquiv N ρ₁ * reciprocityEquiv N ρ₂ := by
  ext a
  simp only [reciprocityEquiv, Equiv.coe_fn_mk, MulChar.ofUnitHom_eq,
    MulChar.equivToUnitHom_symm_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MonoidHom.mul_apply, Units.val_mul, MulChar.mul_apply]

/-- **Langlands reciprocity for `GL(1)` over `ℚ` (the abelian base case).**

There is a bijection between the one-dimensional Galois representations of conductor
dividing `N` (characters of `Gal(ℚ(ζ_N)/ℚ)`) and the automorphic representations of
`GL(1)/ℚ` of level `N` (Dirichlet characters mod `N`), which matches the Frobenius
parameter `ρ(Frob_p)` on the Galois side with the Satake parameter `χ(p)` on the
automorphic side at every unramified place `p ∤ N`.

This is the `n = 1` case of the Langlands reciprocity conjecture; equivalently, it is the
cyclotomic (Kronecker–Weber) form of Artin reciprocity for `ℚ`. -/
