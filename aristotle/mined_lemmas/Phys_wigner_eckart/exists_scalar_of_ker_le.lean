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

theorem exists_scalar_of_ker_le [IsAlgClosed k] [FiniteDimensional k U]
    {ρX : Representation k G V} {ρU : Representation k G U} (hU : IsIrrep ρU)
    {C T : V →ₗ[k] U} (hC : Intertwines ρX ρU C) (hT : Intertwines ρX ρU T)
    (hC0 : C ≠ 0) (hker : ∀ x : V, C x = 0 → T x = 0) :
    ∃ r : k, T = r • C := by
  have hsurj : Function.Surjective C := surjective_of_ne_zero hU hC hC0
  have hle : LinearMap.ker C ≤ LinearMap.ker T := by
    intro x hx
    exact hker x hx
  -- factor `T` through `V ⧸ ker C ≃ U`
  set e := C.quotKerEquivOfSurjective hsurj with he
  set f : U →ₗ[k] U := (Submodule.liftQ (LinearMap.ker C) T hle) ∘ₗ e.symm.toLinearMap with hfdef
  have hfC : ∀ x : V, f (C x) = T x := by
    intro x
    have : e.symm (C x) = Submodule.Quotient.mk x := LinearMap.quotKerEquivOfSurjective_symm_apply _ hsurj x
    simp only [hfdef, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap, this,
      Submodule.liftQ_apply]
  have hfeq : Intertwines ρU ρU f := by
    intro g u
    obtain ⟨x, rfl⟩ := hsurj u
    rw [hfC x, ← hC g x, hfC (ρX g x), hT g x]
  obtain ⟨r, hr⟩ := schur_scalar hU hfeq
  refine ⟨r, ?_⟩
  ext x
  have := hfC x
  rw [hr (C x)] at this
  simpa using this.symm

/-- The subrepresentation of `ρ` carried by an invariant subspace `S`. -/
