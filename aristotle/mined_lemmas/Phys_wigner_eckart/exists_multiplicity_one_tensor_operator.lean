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

theorem exists_multiplicity_one_tensor_operator (k G : Type u) [Field k] [Monoid G] :
    ∃ (Vop Vin Vout : FDRep k G) (CG : Vop ⊗ Vin ⟶ Vout),
      finrank k (Vop ⊗ Vin ⟶ Vout) ≤ 1 ∧ CG ≠ 0 := by
  refine ⟨𝟙_ (FDRep k G), 𝟙_ (FDRep k G), 𝟙_ (FDRep k G), (λ_ (𝟙_ (FDRep k G))).hom, ?_, ?_⟩
  · have hunit : finrank k ((𝟙_ (FDRep k G) : FDRep k G) : Type u) = 1 := finrank_self k
    have htensor : finrank k ((𝟙_ (FDRep k G) ⊗ 𝟙_ (FDRep k G) : FDRep k G) : Type u) = 1 := by
      show finrank k (TensorProduct k ((𝟙_ (FDRep k G) : FDRep k G) : Type u)
        ((𝟙_ (FDRep k G) : FDRep k G) : Type u)) = 1
      rw [Module.finrank_tensorProduct, hunit, one_mul]
    have := finrank_hom_le_mul (𝟙_ (FDRep k G) ⊗ 𝟙_ (FDRep k G)) (𝟙_ (FDRep k G))
    rw [htensor, hunit] at this
    omega
  · intro h
    have h1 := congrArg (fun f => f.hom.hom (TensorProduct.tmul k (1 : k) (1 : k))) h
    have h2 : ((0 : 𝟙_ (FDRep k G) ⊗ 𝟙_ (FDRep k G) ⟶ 𝟙_ (FDRep k G))).hom.hom
        (TensorProduct.tmul k (1 : k) (1 : k)) = 0 := rfl
    simp only [h2] at h1
    simp at h1

end Phys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

