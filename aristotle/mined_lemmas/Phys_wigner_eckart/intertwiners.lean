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

def intertwiners (ρ : Representation k G V) (σ : Representation k G W) :
    Submodule k (V →ₗ[k] W) where
  carrier := {f | ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)}
  zero_mem' := by intro g v; simp
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g v
    simp [h₁ g v, h₂ g v]
  smul_mem' := by
    intro c f h g v
    simp [h g v]

