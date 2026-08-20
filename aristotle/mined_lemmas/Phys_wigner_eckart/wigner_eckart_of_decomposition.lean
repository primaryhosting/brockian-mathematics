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

theorem wigner_eckart_of_decomposition [IsAlgClosed k] [FiniteDimensional k U]
    {ρV : Representation k G V} {ρW : Representation k G W} {ρU : Representation k G U}
    (hU : IsIrrep ρU)
    {M N : Submodule k (V ⊗[k] W)}
    (hMinv : ∀ (g : G), ∀ x ∈ M, (ρV.tprod ρW) g x ∈ M)
    (hNinv : ∀ (g : G), ∀ x ∈ N, (ρV.tprod ρW) g x ∈ N)
    (hMirr : IsIrrep (subrep (ρV.tprod ρW) M hMinv)) (hcompl : IsCompl M N)
    (hNU : ∀ f : N →ₗ[k] U, Intertwines (subrep (ρV.tprod ρW) N hNinv) ρU f → f = 0)
    (CG T : V ⊗[k] W →ₗ[k] U)
    (hCG : Intertwines (ρV.tprod ρW) ρU CG) (hT : Intertwines (ρV.tprod ρW) ρU T)
    (hCG0 : CG ≠ 0) :
    ∃ r : k, T = r • CG ∧
      ∀ (v : V) (w : W) (B : U →ₗ[k] k),
        B (T (v ⊗ₜ[k] w)) = r * B (CG (v ⊗ₜ[k] w)) :=
  wigner_eckart hU CG T hCG hT hCG0
    (ker_le_ker_of_decomposition hMinv hNinv hMirr hcompl hNU hCG hT hCG0)

/-- The trivial one-dimensional representation of any group on `ℂ` is irreducible. -/
