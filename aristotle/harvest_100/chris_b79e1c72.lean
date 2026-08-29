/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {G : Type*} [Group G]

/-- `Intertwines ρ σ f` says that the linear map `f` commutes with the group actions,
i.e. `f` is a morphism of representations (an intertwiner). -/
def Intertwines {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W) : Prop :=
  ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)

/-- A representation is irreducible if the space is nontrivial and the only invariant
subspaces are `⊥` and `⊤`. -/
def IsIrreducibleRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ p : Submodule ℂ V, (∀ (g : G) (v : V), v ∈ p → ρ g v ∈ p) → p = ⊥ ∨ p = ⊤

section Schur

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The kernel of an intertwiner is an invariant subspace. -/
theorem ker_invariant {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} (hf : Intertwines ρ σ f) (g : G) (v : V)
    (hv : v ∈ LinearMap.ker f) : ρ g v ∈ LinearMap.ker f := by
  simp only [LinearMap.mem_ker] at hv ⊢
  rw [hf g v, hv, map_zero]

/-- The range of an intertwiner is an invariant subspace. -/
theorem range_invariant {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} (hf : Intertwines ρ σ f) (g : G) (w : W)
    (hw : w ∈ LinearMap.range f) : σ g w ∈ LinearMap.range f := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨ρ g v, hf g v⟩

/-- **Schur's lemma**, first part: a nonzero intertwiner between irreducible
representations is bijective. -/
theorem schur_bijective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : IsIrreducibleRep ρ) (hσ : IsIrreducibleRep σ)
    {f : V →ₗ[ℂ] W} (hf : Intertwines ρ σ f) (hf0 : f ≠ 0) : Function.Bijective f := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    rcases hρ.2 (LinearMap.ker f) (fun g v hv => ker_invariant hf g v hv) with h | h
    · exact h
    · exact absurd (LinearMap.ext fun v => by
        simpa using LinearMap.mem_ker.1 (h ▸ Submodule.mem_top : v ∈ LinearMap.ker f)) hf0
  · rw [← LinearMap.range_eq_top]
    rcases hσ.2 (LinearMap.range f) (fun g w hw => range_invariant hf g w hw) with h | h
    · exact absurd (LinearMap.ext fun v => by
        have : f v ∈ LinearMap.range f := ⟨v, rfl⟩
        rw [h, Submodule.mem_bot] at this
        simpa using this) hf0
    · exact h

/-- **Schur's lemma**, second part (over the algebraically closed field `ℂ`):
a self-intertwiner of a finite-dimensional irreducible representation is a scalar. -/
theorem schur_scalar [FiniteDimensional ℂ W] {σ : Representation ℂ G W}
    (hσ : IsIrreducibleRep σ) {f : W →ₗ[ℂ] W} (hf : Intertwines σ σ f) :
    ∃ c : ℂ, f = c • LinearMap.id := by
  haveI : Nontrivial W := hσ.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := W) f
  refine ⟨c, ?_⟩
  set h : W →ₗ[ℂ] W := f - c • LinearMap.id with hh
  have hhi : Intertwines σ σ h := by
    intro g v
    simp only [hh, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, hf g v]
  have hker : LinearMap.ker h = ⊥ ∨ LinearMap.ker h = ⊤ :=
    hσ.2 _ (fun g v hv => ker_invariant hhi g v hv)
  have hne : LinearMap.ker h ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
    intro hbot
    apply hv0
    have : v ∈ LinearMap.ker h := by
      simp only [hh, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [Module.End.mem_eigenspace_iff] at hv
      rw [hv, sub_self]
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have htop : LinearMap.ker h = ⊤ := hker.resolve_left hne
  have : h = 0 := by
    ext v
    have : v ∈ LinearMap.ker h := htop ▸ Submodule.mem_top
    simpa using this
  exact sub_eq_zero.mp (by simpa [hh] using this)

end Schur

/-- **Wigner–Eckart theorem.**

Let `U` be the space carrying the components of an irreducible tensor operator, `V` the space
of initial states and `W` the space of final states, all carrying representations of a symmetry
group `G`, with `ρW` irreducible and finite-dimensional.

The "coupling" hypotheses say that `W` occurs exactly once in the tensor product `U ⊗ V`
(the multiplicity-one situation of the classical theorem): it is realized by an intertwiner
`ι : M → U ⊗ V` from an irreducible representation `M`, and every intertwiner `U ⊗ V → W`
vanishing on the image of `ι` vanishes identically.

Fix a nonzero intertwiner `C : U ⊗ V → W`; its matrix elements `bra (C (u ⊗ₜ v))` are the
Clebsch–Gordan coefficients.

Then for *every* intertwiner `T : U ⊗ V → W` (i.e. every tensor operator of this rank) there is
a single constant `c` -- the reduced matrix element -- such that all matrix elements of `T`
factor as a Clebsch–Gordan coefficient times `c`, independently of the operator component `u`,
the initial state `v` and the final state functional `bra`. -/
theorem wigner_eckart
    {U V W M : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ W]
    {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W} {ρM : Representation ℂ G M}
    (hW : IsIrreducibleRep ρW) (hM : IsIrreducibleRep ρM)
    {ι : M →ₗ[ℂ] U ⊗[ℂ] V} (hι : Intertwines ρM (ρU.tprod ρV) ι)
    (hmult : ∀ f : U ⊗[ℂ] V →ₗ[ℂ] W, Intertwines (ρU.tprod ρV) ρW f →
      (∀ m : M, f (ι m) = 0) → f = 0)
    {C : U ⊗[ℂ] V →ₗ[ℂ] W} (hC : Intertwines (ρU.tprod ρV) ρW C) (hC0 : C ≠ 0)
    {T : U ⊗[ℂ] V →ₗ[ℂ] W} (hT : Intertwines (ρU.tprod ρV) ρW T) :
    ∃ c : ℂ, ∀ (bra : W →ₗ[ℂ] ℂ) (u : U) (v : V),
      bra (T (u ⊗ₜ[ℂ] v)) = c * bra (C (u ⊗ₜ[ℂ] v)) := by
  -- The restriction of the Clebsch-Gordan intertwiner to the coupled copy of `W`.
  set e : M →ₗ[ℂ] W := C ∘ₗ ι with he
  have heI : Intertwines ρM ρW e := by
    intro g m
    simp only [he, LinearMap.comp_apply, hι g m, hC g (ι m)]
  have he0 : e ≠ 0 := by
    intro h0
    refine hC0 (hmult C hC fun m => ?_)
    have := congrArg (fun F : M →ₗ[ℂ] W => F m) h0
    simpa [he] using this
  have hbij : Function.Bijective e := schur_bijective hM hW heI he0
  set E : M ≃ₗ[ℂ] W := LinearEquiv.ofBijective e hbij with hE
  have hEapply : ∀ m : M, E m = e m := fun m => rfl
  have hEsymm : Intertwines ρW ρM (E.symm : W →ₗ[ℂ] M) := by
    intro g w
    apply hbij.1
    have h1 : e (E.symm (ρW g w)) = ρW g w := by
      rw [← hEapply]; exact E.apply_symm_apply _
    have h2 : e (E.symm w) = w := by
      rw [← hEapply]; exact E.apply_symm_apply _
    show e (E.symm (ρW g w)) = e (ρM g (E.symm w))
    rw [h1, heI g (E.symm w), h2]
  have hTι : Intertwines ρM ρW (T ∘ₗ ι) := by
    intro g m
    simp only [LinearMap.comp_apply, hι g m, hT g (ι m)]
  set F : W →ₗ[ℂ] W := (T ∘ₗ ι) ∘ₗ (E.symm : W →ₗ[ℂ] M) with hF
  have hFI : Intertwines ρW ρW F := by
    intro g w
    have h1 : (E.symm : W →ₗ[ℂ] M) (ρW g w) = ρM g ((E.symm : W →ₗ[ℂ] M) w) := hEsymm g w
    simp only [hF, LinearMap.comp_apply, h1]
    simpa using hTι g ((E.symm : W →ₗ[ℂ] M) w)
  obtain ⟨c, hc⟩ := schur_scalar hW hFI
  have hTC : T = c • C := by
    have hzero : T - c • C = 0 := by
      refine hmult (T - c • C) ?_ ?_
      · intro g x
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hT g x, hC g x]
      · intro m
        have hsm : (E.symm : W →ₗ[ℂ] M) (e m) = m := by
          have : (E.symm : W →ₗ[ℂ] M) (E m) = m := E.symm_apply_apply m
          rwa [hEapply] at this
        have h1 : F (e m) = T (ι m) := by
          simp only [hF, LinearMap.comp_apply, hsm]
        have h2 : F (e m) = c • e m := by
          rw [hc]; simp
        have h3 : T (ι m) = c • C (ι m) := by
          rw [← h1, h2, he]; rfl
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, h3, sub_self]
    exact sub_eq_zero.mp hzero
  refine ⟨c, fun bra u v => ?_⟩
  rw [hTC]
  simp [smul_eq_mul]

section Nonvacuous

/-! ### A sanity check: the hypotheses of `wigner_eckart` are satisfiable. -/

/-- Over a field, the only submodules are `⊥` and `⊤`, so the trivial one-dimensional
representation is irreducible. -/
theorem isIrreducibleRep_one_complex {G : Type*} [Group G] :
    IsIrreducibleRep (1 : Representation ℂ G ℂ) := by
  refine ⟨inferInstance, fun p _ => ?_⟩
  by_cases hp : p = ⊥
  · exact Or.inl hp
  · refine Or.inr ?_
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    refine eq_top_iff.2 fun y _ => ?_
    have : (y / x) • x ∈ p := p.smul_mem _ hx
    rwa [smul_eq_mul, div_mul_cancel₀ _ hx0] at this

/-- All the hypotheses of `wigner_eckart` are simultaneously satisfiable:
the theorem is not vacuous. -/
theorem wigner_eckart_hypotheses_satisfiable {G : Type*} [Group G] :
    ∃ (ι : ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℂ) (C : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ),
      IsIrreducibleRep (1 : Representation ℂ G ℂ) ∧
      Intertwines (1 : Representation ℂ G ℂ)
        ((1 : Representation ℂ G ℂ).tprod (1 : Representation ℂ G ℂ)) ι ∧
      (∀ f : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ,
        Intertwines ((1 : Representation ℂ G ℂ).tprod (1 : Representation ℂ G ℂ))
          (1 : Representation ℂ G ℂ) f → (∀ m : ℂ, f (ι m) = 0) → f = 0) ∧
      Intertwines ((1 : Representation ℂ G ℂ).tprod (1 : Representation ℂ G ℂ))
        (1 : Representation ℂ G ℂ) C ∧ C ≠ 0 := by
  refine ⟨(TensorProduct.lid ℂ ℂ).symm.toLinearMap, (TensorProduct.lid ℂ ℂ).toLinearMap,
    isIrreducibleRep_one_complex, ?_, ?_, ?_, ?_⟩
  · intro g m; simp
  · intro f _ hf
    refine TensorProduct.ext' fun x y => ?_
    have hxy : (x ⊗ₜ[ℂ] y : ℂ ⊗[ℂ] ℂ) = (TensorProduct.lid ℂ ℂ).symm (x * y) :=
      calc (x ⊗ₜ[ℂ] y : ℂ ⊗[ℂ] ℂ) = (x • (1 : ℂ)) ⊗ₜ[ℂ] y := by rw [smul_eq_mul, mul_one]
        _ = (1 : ℂ) ⊗ₜ[ℂ] (x • y) := TensorProduct.smul_tmul _ _ _
        _ = (TensorProduct.lid ℂ ℂ).symm (x * y) := by
              rw [TensorProduct.lid_symm_apply, smul_eq_mul]
    rw [hxy]
    simpa using hf (x * y)
  · intro g x; simp
  · intro h
    have := congrArg (fun F : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ => F ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))) h
    simp at this

end Nonvacuous

end Phys

