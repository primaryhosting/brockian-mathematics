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

theorem lid_ne_zero : (TensorProduct.lid ℂ ℂ).toLinearMap ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : (ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ => f (1 ⊗ₜ[ℂ] 1)) h
  simp at h1

/-- A concrete, non-vacuous instance of the Wigner–Eckart theorem. -/
