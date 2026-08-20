/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `Phys.Intertwines`, `Phys.IsIrrep` : equivariant maps and irreducible representations.
* `Phys.schur_scalar` : Schur's lemma (endomorphism form).
* `Phys.exists_scalar_of_ker_le` : uniqueness of intertwiners up to scale.
* `Phys.wigner_eckart` : the Wigner–Eckart theorem.
* `Phys.wigner_eckart_of_decomposition` : the same, with multiplicity one supplied as a
  direct-sum decomposition of the coupled space.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Phys

variable {k G V W U : Type*}
  [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- `Intertwines ρ σ f` says that the linear map `f` is equivariant (a morphism of
representations) from `ρ` to `σ`: `f ∘ ρ g = σ g ∘ f` for all group elements `g`. -/

theorem intertwines_comp_subtype {ρ : Representation k G V} {σ : Representation k G U}
    {S : Submodule k V} (h : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) {f : V →ₗ[k] U}
    (hf : Intertwines ρ σ f) : Intertwines (subrep ρ S h) σ (f ∘ₗ S.subtype) := by
  intro g v
  simpa using hf g (v : V)

/-- **Multiplicity one gives the kernel hypothesis.**  Suppose the source representation splits
as a direct sum of an irreducible piece `M` and a complement `N` that contains no copy of the
irreducible target `ρU` (i.e. every intertwiner out of `N` vanishes).  Then any two intertwiners
into `U` have comparable kernels: `T` annihilates everything a nonzero `CG` annihilates. -/
