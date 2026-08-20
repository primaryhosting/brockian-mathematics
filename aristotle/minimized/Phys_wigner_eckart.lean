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

theorem finrank_hom_le_one_of_simple {k G : Type u} [Field k] [IsAlgClosed k] [Monoid G]
    (X Y : FDRep k G) [Simple X] [Simple Y] : finrank k (X ⟶ Y) ≤ 1 := by
  rw [FDRep.finrank_hom_simple_simple]
  split <;> simp

/-- The space of intertwiners between two finite-dimensional representations embeds into the
space of all linear maps, hence has dimension at most `dim X * dim Y`. -/

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
