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
