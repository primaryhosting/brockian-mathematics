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
