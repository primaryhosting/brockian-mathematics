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

def rangeSubrep {ρ : Representation k G M} {σ : Representation k G N}
    (C : M →ₗ[k] N) (hC : ∀ g x, C (ρ g x) = σ g (C x)) : Subrepresentation σ where
  toSubmodule := LinearMap.range C
  apply_mem_toSubmodule g := by
    rintro v ⟨x, rfl⟩
    exact ⟨ρ g x, hC g x⟩

omit [IsAlgClosed k] in
/-- An intertwining map into an irreducible representation is surjective, unless it is zero. -/
