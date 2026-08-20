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
private lemma exists_smul_of_finrank_le_one {k E : Type*} [Field k] [AddCommGroup E] [Module k E]
    [FiniteDimensional k E] (h : finrank k E ≤ 1) {c : E} (hc : c ≠ 0) (t : E) :
    ∃ r : k, t = r • c := by
  have h1 : finrank k (Submodule.span k {c}) = 1 := finrank_span_singleton hc
  have hle : finrank k (Submodule.span k {c}) ≤ finrank k E := Submodule.finrank_le _
  have h2 : Submodule.span k ({c} : Set E) = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have ht : t ∈ Submodule.span k ({c} : Set E) := by rw [h2]; trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ht
  exact ⟨r, hr.symm⟩

/-- A nonzero vector of a finite-dimensional space is detected by some linear functional. -/
private lemma exists_functional_ne_zero {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {w : V} (hw : w ≠ 0) : ∃ f : V →ₗ[k] k, f w ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hw ((Module.Basis.forall_coord_eq_zero_iff (Module.Free.chooseBasis k V)).mp
    fun i => hc _)

/-- An intertwiner of representations which kills every vector is the zero intertwiner. -/
private lemma hom_eq_zero_of_apply_eq_zero {k G : Type u} [Field k] [Monoid G] {X Y : FDRep k G}
    {f : X ⟶ Y} (h : ∀ v : X, f.hom.hom v = 0) : f = 0 := by
  ext v
  simpa using h v

/-- **Multiplicity one from Schur's lemma.** Between two irreducible finite-dimensional
representations over an algebraically closed field, the space of intertwiners is at most
one-dimensional. This is `FDRep.finrank_hom_simple_simple`. -/
theorem finrank_hom_le_one_of_simple {k G : Type u} [Field k] [IsAlgClosed k] [Monoid G]
    (X Y : FDRep k G) [Simple X] [Simple Y] : finrank k (X ⟶ Y) ≤ 1 := by
  rw [FDRep.finrank_hom_simple_simple]
  split <;> simp

/-- The space of intertwiners between two finite-dimensional representations embeds into the
space of all linear maps, hence has dimension at most `dim X * dim Y`. -/
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
theorem exists_reduced_matrix_element {k G : Type u} [Field k] [Monoid G] {X Y : FDRep k G}
    (hmult : finrank k (X ⟶ Y) ≤ 1) {CG : X ⟶ Y} (hCG : CG ≠ 0) (T : X ⟶ Y) :
    ∃ reduced : k, ∀ (bra : Y →ₗ[k] k) (v : X),
      bra (T.hom.hom v) = reduced * bra (CG.hom.hom v) := by
  obtain ⟨r, hr⟩ := exists_smul_of_finrank_le_one hmult hCG T
  refine ⟨r, fun bra v => ?_⟩
  have hv : T.hom.hom v = r • CG.hom.hom v := by rw [hr]; rfl
  rw [hv, map_smul, smul_eq_mul]

/-- **The Wigner–Eckart theorem.**

Let `Vop` be the representation carried by the components of a tensor operator (rank `k` in
the physics notation), `Vin` the initial multiplet and `Vout` the final multiplet, all
finite-dimensional representations of a group (or monoid) `G`. A tensor operator, viewed
between these multiplets, is an equivariant map `T : Vop ⊗ Vin ⟶ Vout`, and `CG` is a fixed
nonzero equivariant map, the Clebsch–Gordan map. Assuming multiplicity one, i.e. that the
space of equivariant maps `Vop ⊗ Vin ⟶ Vout` is at most one-dimensional (automatic for
irreducible source and target by Schur's lemma, see `Phys.finrank_hom_le_one_of_simple`),
there is a single scalar `reduced` — the reduced matrix element `⟨Vout ‖ T ‖ Vin⟩`, depending
on neither the operator component `q`, nor the initial state `m`, nor the final state `bra` —
such that every matrix element of `T` is the corresponding Clebsch–Gordan coefficient times
`reduced`:

`⟨bra | T (q ⊗ m)⟩ = reduced * ⟨bra | CG (q ⊗ m)⟩`. -/
theorem wigner_eckart {k G : Type u} [Field k] [Monoid G] {Vop Vin Vout : FDRep k G}
    (hmult : finrank k (Vop ⊗ Vin ⟶ Vout) ≤ 1)
    {CG : Vop ⊗ Vin ⟶ Vout} (hCG : CG ≠ 0) (T : Vop ⊗ Vin ⟶ Vout) :
    ∃ reduced : k, ∀ (bra : Vout →ₗ[k] k) (q : Vop) (m : Vin),
      bra (T.hom.hom (TensorProduct.tmul k q m))
        = reduced * bra (CG.hom.hom (TensorProduct.tmul k q m)) := by
  obtain ⟨reduced, h⟩ := exists_reduced_matrix_element hmult hCG T
  exact ⟨reduced, fun bra q m => h bra _⟩

/-- The Wigner–Eckart theorem in the case where multiplicity one is supplied by Schur's lemma
(irreducible source and target over an algebraically closed field) rather than assumed. -/
theorem wigner_eckart_of_simple {k G : Type u} [Field k] [IsAlgClosed k] [Monoid G]
    {Vop Vin Vout : FDRep k G} [Simple (Vop ⊗ Vin)] [Simple Vout]
    {CG : Vop ⊗ Vin ⟶ Vout} (hCG : CG ≠ 0) (T : Vop ⊗ Vin ⟶ Vout) :
    ∃ reduced : k, ∀ (bra : Vout →ₗ[k] k) (q : Vop) (m : Vin),
      bra (T.hom.hom (TensorProduct.tmul k q m))
        = reduced * bra (CG.hom.hom (TensorProduct.tmul k q m)) :=
  wigner_eckart (finrank_hom_le_one_of_simple _ _) hCG T

/-- The reduced matrix element is unique: two scalars that both factor all matrix elements of
`T` through those of a nonzero `CG` are equal. In particular the conclusion of
`Phys.wigner_eckart` pins `reduced` down. -/
theorem reduced_matrix_element_unique {k G : Type u} [Field k] [Monoid G] {X Y : FDRep k G}
    {CG : X ⟶ Y} (hCG : CG ≠ 0) {T : X ⟶ Y} {r r' : k}
    (hr : ∀ (bra : Y →ₗ[k] k) (v : X), bra (T.hom.hom v) = r * bra (CG.hom.hom v))
    (hr' : ∀ (bra : Y →ₗ[k] k) (v : X), bra (T.hom.hom v) = r' * bra (CG.hom.hom v)) :
    r = r' := by
  obtain ⟨v, hv⟩ : ∃ v : X, CG.hom.hom v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hCG (hom_eq_zero_of_apply_eq_zero hc)
  obtain ⟨bra, hbra⟩ := exists_functional_ne_zero (k := k) hv
  have := (hr bra v).symm.trans (hr' bra v)
  exact mul_right_cancel₀ hbra this

/-- The hypotheses of `Phys.wigner_eckart` are not vacuous: for any field `k` and monoid `G`
there are representations and a nonzero Clebsch–Gordan map satisfying multiplicity one (take
all three multiplets to be the trivial one-dimensional representation, with `CG` the left
unitor). -/
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

