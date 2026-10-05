import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma finalMem_prodComm (beta : ℝ) (E : Bool → ℝ) (m : Bool) :
    finalMem beta E (fun _ => (1 / 2 : ℝ)) (Equiv.prodComm Bool Bool) m
      = gibbs beta E m := by
  unfold finalMem finalJoint initJoint
  simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [Fintype.sum_bool]
  ring

/-! ## Auxiliary entropy estimates -/

