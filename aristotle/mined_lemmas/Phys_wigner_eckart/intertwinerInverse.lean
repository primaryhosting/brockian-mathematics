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

noncomputable def intertwinerInverse {ρ : Representation k G V} {σ : Representation k G W}
    (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) : IntertwiningMap σ ρ where
  toLinearMap := (LinearEquiv.ofBijective f.toLinearMap hf).symm
  isIntertwining' g w := by
    have key : ∀ x : W, f ((LinearEquiv.ofBijective f.toLinearMap hf).symm x) = x :=
      fun x => (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x
    apply hf.injective
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm ((σ g) w))
      = f ((ρ g) ((LinearEquiv.ofBijective f.toLinearMap hf).symm w))
    rw [key, f.isIntertwining, key]

