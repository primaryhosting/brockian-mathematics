/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace Phys

open Representation

variable {k G M N : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The range of an intertwining map, as a subrepresentation of the target. -/

theorem wigner_eckart_nonvacuous (G : Type*) [Group G] :
    ∃! r : ℂ, ∀ (bra : ℂ →ₗ[ℂ] ℂ) (u v : ℂ),
      bra ((TensorProduct.lid ℂ ℂ) (u ⊗ₜ[ℂ] v)) =
        r * bra ((TensorProduct.lid ℂ ℂ) (u ⊗ₜ[ℂ] v)) := by
  have hequiv : ∀ (g : G) (x : ℂ ⊗[ℂ] ℂ),
      (TensorProduct.lid ℂ ℂ).toLinearMap
          (((Representation.trivial ℂ G ℂ).tprod (Representation.trivial ℂ G ℂ)) g x) =
        (Representation.trivial ℂ G ℂ) g ((TensorProduct.lid ℂ ℂ).toLinearMap x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simp [Representation.tprod_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hne : (TensorProduct.lid ℂ ℂ).toLinearMap ≠ 0 := by
    intro h
    have : (TensorProduct.lid ℂ ℂ).toLinearMap ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by rw [h]; rfl
    simp at this
  exact wigner_eckart (Representation.trivial ℂ G ℂ) (Representation.trivial ℂ G ℂ)
    (Representation.trivial ℂ G ℂ) _ _ hequiv hequiv hne (fun _ h => h)

end NonVacuous

end Phys

import Mathlib

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

