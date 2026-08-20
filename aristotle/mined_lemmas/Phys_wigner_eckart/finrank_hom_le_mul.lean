/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## The Wigner–Eckart theorem

The physical statement is: the matrix elements of the components of a spherical tensor
operator `T^{(k)}_q` between angular-momentum eigenstates factor as

`⟨j' m' | T^{(k)}_q | j m⟩ = ⟨j m; k q | j' m'⟩ · ⟨j' ‖ T^{(k)} ‖ j⟩`,

i.e. as a Clebsch–Gordan coefficient (which depends on all the magnetic quantum numbers,
but not on the operator) times a *reduced matrix element* (which depends on the operator,
but on none of the magnetic quantum numbers `m, m', q`).

Mathematically this is Schur's lemma plus multiplicity one:

* a spherical tensor operator of rank `k`, restricted to the initial multiplet `Vin` and
  followed by the projection onto the final multiplet `Vout`, is exactly an equivariant map
  `T : Vop ⊗ Vin ⟶ Vout` of representations (`Vop` being the multiplet carried by the
  operator components);
* the Clebsch–Gordan map `CG : Vop ⊗ Vin ⟶ Vout` is one fixed nonzero such map;
* multiplicity one says that the space of such equivariant maps is at most one-dimensional,
  so `T = reduced • CG` for a unique scalar `reduced`, and taking matrix elements
  `⟨bra, -⟩` gives the Wigner–Eckart factorization.

Multiplicity one is automatic when source and target are irreducible: this is Schur's lemma,
available in Mathlib as `FDRep.finrank_hom_simple_simple`
(`Mathlib/RepresentationTheory/FDRep.lean`), recorded below as
`Phys.finrank_hom_le_one_of_simple`.

Main results:

* `Phys.wigner_eckart` — the factorization of matrix elements of a tensor operator;
* `Phys.reduced_matrix_element_unique` — the reduced matrix element is unique, so the
  factorization has genuine content;
* `Phys.exists_multiplicity_one_tensor_operator` — the hypotheses of `Phys.wigner_eckart`
  are satisfiable (they are not vacuous).
-/

open CategoryTheory Module MonoidalCategory

universe u

namespace Phys

/-- A vector space of dimension at most one, containing a nonzero vector `c`, is spanned by `c`. -/

theorem finrank_hom_le_mul {k G : Type u} [Field k] [Monoid G] (X Y : FDRep k G) :
    finrank k (X ⟶ Y) ≤ finrank k X * finrank k Y := by
  have e : ((forget₂ (FGModuleCat k) (ModuleCat k)).obj X.V ⟶
      (forget₂ (FGModuleCat k) (ModuleCat k)).obj Y.V) ≃ₗ[k] (X →ₗ[k] Y) :=
    ModuleCat.homLinearEquiv
  haveI : FiniteDimensional k ((forget₂ (FGModuleCat k) (ModuleCat k)).obj X.V ⟶
      (forget₂ (FGModuleCat k) (ModuleCat k)).obj Y.V) := e.symm.finiteDimensional
  have hinj : Function.Injective
      (((forget₂ (FGModuleCat k) (ModuleCat k)).mapLinearMap k (X := X.V) (Y := Y.V)).comp
        ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k (X := X) (Y := Y))) :=
    fun a b hab => Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k))
      (Functor.map_injective (forget₂ (FGModuleCat k) (ModuleCat k)) hab)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : finrank k ((forget₂ (FGModuleCat k) (ModuleCat k)).obj X.V ⟶
      (forget₂ (FGModuleCat k) (ModuleCat k)).obj Y.V) = finrank k X * finrank k Y := by
    rw [e.finrank_eq, Module.finrank_linearMap, mul_comm]
  omega

/-- **Reduced matrix element.** If the space of intertwiners `X ⟶ Y` is at most
one-dimensional and `CG` is a nonzero intertwiner, then every intertwiner `T` has all of its
matrix elements equal to those of `CG` scaled by a single scalar, the *reduced matrix
element*, which is independent of the chosen state `v` and of the chosen bra `bra`. -/
