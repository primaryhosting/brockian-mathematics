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
def Intertwines (ρ : Representation k G V) (σ : Representation k G U)
    (f : V →ₗ[k] U) : Prop :=
  ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)

/-- A representation is irreducible if the underlying space is nonzero and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/
structure IsIrrep (ρ : Representation k G V) : Prop where
  nontrivial : ∃ v : V, v ≠ 0
  simple : ∀ S : Submodule k V, (∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤

theorem IsIrrep.nontrivial' {ρ : Representation k G V} (h : IsIrrep ρ) : Nontrivial V := by
  obtain ⟨v, hv⟩ := h.nontrivial
  exact ⟨⟨v, 0, hv⟩⟩

/-- **Schur's lemma, endomorphism form.** An equivariant endomorphism of a finite-dimensional
irreducible representation over an algebraically closed field is a scalar. -/
theorem schur_scalar [IsAlgClosed k] [FiniteDimensional k U] {ρU : Representation k G U}
    (hU : IsIrrep ρU) {f : U →ₗ[k] U} (hf : Intertwines ρU ρU f) :
    ∃ c : k, ∀ u : U, f u = c • u := by
  haveI : Nontrivial U := hU.nontrivial'
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f : Module.End k U)
  obtain ⟨x, hx, hx0⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  set S : Submodule k U := LinearMap.ker (f - c • LinearMap.id) with hS
  have hxS : x ∈ S := by
    have : f x = c • x := Module.End.mem_eigenspace_iff.mp hx
    simp [hS, LinearMap.mem_ker, this]
  have hinv : ∀ (g : G), ∀ u ∈ S, ρU g u ∈ S := by
    intro g u hu
    have hu' : f u = c • u := by
      have := hu
      simp only [hS, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] at this
      exact this
    simp only [hS, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    rw [hf g u, hu', map_smul]
  rcases hU.simple S hinv with h | h
  · exact absurd (by simpa [h] using hxS) hx0
  · intro u
    have : u ∈ S := by simp [h]
    simp only [hS, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at this
    exact this

/-- An equivariant map onto an irreducible representation is either zero or surjective. -/
theorem surjective_of_ne_zero {ρX : Representation k G V} {ρU : Representation k G U}
    (hU : IsIrrep ρU) {C : V →ₗ[k] U} (hC : Intertwines ρX ρU C) (hC0 : C ≠ 0) :
    Function.Surjective C := by
  have hinv : ∀ (g : G), ∀ u ∈ LinearMap.range C, ρU g u ∈ LinearMap.range C := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρX g v, hC g v⟩
  rcases hU.simple (LinearMap.range C) hinv with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) hC0
  · rw [← LinearMap.range_eq_top]; exact h

/-- **Schur's lemma, uniqueness of intertwiners up to scale.** If `C` and `T` are equivariant
maps into a finite-dimensional irreducible representation over an algebraically closed field,
`C ≠ 0`, and `T` vanishes wherever `C` does (the multiplicity-one hypothesis), then `T` is a
scalar multiple of `C`. -/
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
def subrep (ρ : Representation k G V) (S : Submodule k V)
    (h : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) : Representation k G S where
  toFun g := LinearMap.restrict (ρ g) (h g)
  map_one' := by ext v; simp
  map_mul' g g' := by ext v; simp

@[simp] theorem subrep_apply_coe (ρ : Representation k G V) (S : Submodule k V)
    (h : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : S) :
    ((subrep ρ S h g v : S) : V) = ρ g (v : V) := rfl

/-- Restricting an intertwiner to an invariant subspace gives an intertwiner. -/
theorem intertwines_comp_subtype {ρ : Representation k G V} {σ : Representation k G U}
    {S : Submodule k V} (h : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) {f : V →ₗ[k] U}
    (hf : Intertwines ρ σ f) : Intertwines (subrep ρ S h) σ (f ∘ₗ S.subtype) := by
  intro g v
  simpa using hf g (v : V)

/-- **Multiplicity one gives the kernel hypothesis.**  Suppose the source representation splits
as a direct sum of an irreducible piece `M` and a complement `N` that contains no copy of the
irreducible target `ρU` (i.e. every intertwiner out of `N` vanishes).  Then any two intertwiners
into `U` have comparable kernels: `T` annihilates everything a nonzero `CG` annihilates. -/
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
theorem wigner_eckart [IsAlgClosed k] [FiniteDimensional k U]
    {ρV : Representation k G V} {ρW : Representation k G W} {ρU : Representation k G U}
    (hU : IsIrrep ρU)
    (CG T : V ⊗[k] W →ₗ[k] U)
    (hCG : Intertwines (ρV.tprod ρW) ρU CG) (hT : Intertwines (ρV.tprod ρW) ρU T)
    (hCG0 : CG ≠ 0)
    (hmult : ∀ x : V ⊗[k] W, CG x = 0 → T x = 0) :
    ∃ r : k, T = r • CG ∧
      ∀ (v : V) (w : W) (B : U →ₗ[k] k),
        B (T (v ⊗ₜ[k] w)) = r * B (CG (v ⊗ₜ[k] w)) := by
  obtain ⟨r, hr⟩ := exists_scalar_of_ker_le hU hCG hT hCG0 hmult
  refine ⟨r, hr, ?_⟩
  intro v w B
  rw [hr]
  simp

/-- **Wigner–Eckart theorem, multiplicity-one form.**  Here the multiplicity-one hypothesis is
supplied in its usual representation-theoretic shape: the coupled space `V ⊗ W` splits as a
direct sum of a single irreducible piece `M` (the copy of the final-state representation that
the Clebsch–Gordan map picks out) and a complement `N` containing no copy of `ρU`. -/
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
theorem isIrrep_one_complex {G : Type*} [Group G] : IsIrrep (1 : Representation ℂ G ℂ) where
  nontrivial := ⟨1, one_ne_zero⟩
  simple := fun S _ => by
    haveI : IsSimpleModule ℂ ℂ := inferInstance
    exact eq_bot_or_eq_top S

/-- The hypotheses of `Phys.wigner_eckart` are satisfiable: they hold for the trivial
one-dimensional representations with the Clebsch–Gordan map `1 ⊗ 1 ↦ 1`. -/
theorem wigner_eckart_hypotheses_satisfiable (G : Type*) [Group G] :
    ∃ CG T : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ,
      Intertwines ((1 : Representation ℂ G ℂ).tprod 1) 1 CG ∧
      Intertwines ((1 : Representation ℂ G ℂ).tprod 1) 1 T ∧
      CG ≠ 0 ∧ ∀ x : ℂ ⊗[ℂ] ℂ, CG x = 0 → T x = 0 := by
  refine ⟨(TensorProduct.lid ℂ ℂ).toLinearMap, (TensorProduct.lid ℂ ℂ).toLinearMap,
    ?_, ?_, ?_, fun x hx => hx⟩
  · intro g v; simp [Representation.tprod_apply]
  · intro g v; simp [Representation.tprod_apply]
  · intro h
    have : (TensorProduct.lid ℂ ℂ).toLinearMap ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by rw [h]; rfl
    simp at this

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

