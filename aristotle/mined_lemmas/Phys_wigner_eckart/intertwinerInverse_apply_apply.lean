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

@[simp] lemma intertwinerInverse_apply_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) (v : V) :
    intertwinerInverse f hf (f v) = v :=
  (LinearEquiv.ofBijective f.toLinearMap hf).symm_apply_apply v

/-- **Proportionality of intertwiners in a multiplicity-one situation.**
If the space of intertwiners `ρ → σ` is at most one dimensional and `CG` is a nonzero
intertwiner, then every intertwiner is a scalar multiple of `CG`. -/
