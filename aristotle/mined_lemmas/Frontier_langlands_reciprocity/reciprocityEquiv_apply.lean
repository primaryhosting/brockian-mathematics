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

theorem reciprocityEquiv_apply (ρ : GaloisChar N) (v : UnramifiedPlace N) :
    reciprocityEquiv N ρ (v.1 : ZMod N) = (ρ (frob N v) : ℂ) := by
  have : ((v.1 : ℕ) : ZMod N)
      = ((ZMod.unitOfCoprime v.1 (UnramifiedPlace.coprime N v) : (ZMod N)ˣ) : ZMod N) := by
    rw [ZMod.coe_unitOfCoprime]
  rw [this, reciprocityEquiv]
  simp only [Equiv.coe_fn_mk, MulChar.ofUnitHom_eq, MulChar.equivToUnitHom_symm_coe,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, frob]

/-- The reciprocity bijection is compatible with twisting: it is multiplicative. -/
