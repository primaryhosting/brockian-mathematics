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

@[simp] lemma mem_intertwiners {ρ : Representation k G V} {σ : Representation k G W}
    {f : V →ₗ[k] W} : f ∈ intertwiners ρ σ ↔ ∀ (g : G) (v : V), f (ρ g v) = σ g (f v) := Iff.rfl

/-- Bundling a member of `Phys.intertwiners` as a Mathlib `Representation.IntertwiningMap`. -/
