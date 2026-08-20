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

open scoped TensorProduct

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A (complex) representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/

def IsIrrep (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ U : Submodule ℂ V, (∀ (g : G) (v : V), v ∈ U → ρ g v ∈ U) → U = ⊥ ∨ U = ⊤

/-- `T` intertwines the representations `ρ` and `σ` (i.e. it is an operator transforming
covariantly: `T ∘ ρ g = σ g ∘ T`).  For `V = V_k ⊗ V_j` this is exactly the statement that the
components `T_q` form an irreducible tensor operator of rank `k`. -/
