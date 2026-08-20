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

theorem ker_le_ker_of_decomposition {ρX : Representation k G V} {ρU : Representation k G U}
    {M N : Submodule k V}
    (hMinv : ∀ (g : G), ∀ v ∈ M, ρX g v ∈ M) (hNinv : ∀ (g : G), ∀ v ∈ N, ρX g v ∈ N)
    (hMirr : IsIrrep (subrep ρX M hMinv)) (hcompl : IsCompl M N)
    (hNU : ∀ f : N →ₗ[k] U, Intertwines (subrep ρX N hNinv) ρU f → f = 0)
    {CG T : V →ₗ[k] U} (hCG : Intertwines ρX ρU CG) (hT : Intertwines ρX ρU T)
    (hCG0 : CG ≠ 0) :
    ∀ x : V, CG x = 0 → T x = 0 := by
  -- both intertwiners vanish on `N`
  have hvanish : ∀ (f : V →ₗ[k] U), Intertwines ρX ρU f → ∀ n ∈ N, f n = 0 := by
    intro f hf n hn
    have := hNU _ (intertwines_comp_subtype hNinv hf)
    have h2 := congrArg (fun (F : N →ₗ[k] U) => F ⟨n, hn⟩) this
    simpa using h2
  -- `CG` is injective on `M`
  have hCGM : Function.Injective (CG ∘ₗ M.subtype) := by
    have hker : ∀ (g : G), ∀ v ∈ LinearMap.ker (CG ∘ₗ M.subtype),
        subrep ρX M hMinv g v ∈ LinearMap.ker (CG ∘ₗ M.subtype) := by
      intro g v hv
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype] at hv ⊢
      rw [subrep_apply_coe, hCG g (v : V), hv, map_zero]
    rcases hMirr.simple _ hker with h | h
    · rw [← LinearMap.ker_eq_bot]; exact h
    · exfalso
      refine hCG0 ?_
      ext x
      obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top :
        x ∈ M ⊔ N)
      have hm0 : CG m = 0 := by
        have : (⟨m, hm⟩ : M) ∈ LinearMap.ker (CG ∘ₗ M.subtype) := by rw [h]; trivial
        simpa using this
      simp [map_add, hm0, hvanish CG hCG n hn]
  intro x hx
  obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top :
    x ∈ M ⊔ N)
  have hm0 : m = 0 := by
    have : (CG ∘ₗ M.subtype) ⟨m, hm⟩ = (CG ∘ₗ M.subtype) 0 := by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, map_zero]
      rw [map_add, hvanish CG hCG n hn, add_zero] at hx
      exact hx
    simpa using congrArg Subtype.val (hCGM this)
  rw [hm0, zero_add, hvanish T hT n hn]

/-- **Wigner–Eckart theorem.**

Let `ρV`, `ρW`, `ρU` be representations of a symmetry group `G` on `k`-vector spaces (`k`
algebraically closed, e.g. `ℂ`), with `ρU` irreducible and `U` finite-dimensional.  Think of
`V` as the space carrying the components `T_q` of a tensor operator, `W` as the space of
initial states and `U` as the space of final states.

Let `CG : V ⊗ W →ₗ U` be a fixed nonzero equivariant map (the Clebsch–Gordan map, coupling the
tensor operator to the initial state) and let `T : V ⊗ W →ₗ U` be the equivariant map attached
to an arbitrary tensor operator.  Assume multiplicity one, in the form that `T` annihilates
everything that `CG` annihilates.

Then there is a single scalar `r` — the *reduced matrix element*, independent of `v`, `w` and of
the final-state functional `B` — such that every matrix element factors as a Clebsch–Gordan
coefficient times `r`:
`⟨B | T (v ⊗ w)⟩ = r * ⟨B | CG (v ⊗ w)⟩`. -/
