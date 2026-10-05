/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct
open Representation

namespace Phys

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The space of intertwining (`G`-equivariant) linear maps between two representations,
as a subspace of all linear maps. -/

theorem wigner_eckart_trivial (T : (ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ)
    (hT : T ∈ intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ)) :
    ∃ red : ℂ, T = red • (TensorProduct.lid ℂ ℂ).toLinearMap ∧ ∀ (φ : ℂ →ₗ[ℂ] ℂ) (u v : ℂ),
      φ (T (u ⊗ₜ[ℂ] v)) = red * φ ((TensorProduct.lid ℂ ℂ) (u ⊗ₜ[ℂ] v)) :=
  wigner_eckart (rank_intertwiners_trivial_le_one Γ) _ T
    (lid_mem_intertwiners_trivial Γ) hT lid_ne_zero

end Concrete

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

