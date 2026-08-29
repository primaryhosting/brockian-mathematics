/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {G : Type*} [Group G]

/-- `Intertwines ρ σ f` says that the linear map `f` commutes with the group actions,
i.e. `f` is a morphism of representations (an intertwiner). -/

def IsIrreducibleRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ p : Submodule ℂ V, (∀ (g : G) (v : V), v ∈ p → ρ g v ∈ p) → p = ⊥ ∨ p = ⊤

section Schur

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The kernel of an intertwiner is an invariant subspace. -/
