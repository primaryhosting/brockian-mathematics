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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The Wigner–Eckart theorem

Physics setting.  A *tensor operator* of rank `k` acting between two irreducible multiplets
`j'` and `j` is a family of operators `T^k_q` obeying the covariance law

  `U(g) T^k_q U(g)⁻¹ = ∑_{q'} D^k(g)_{q' q} T^k_{q'}`.

Equivalently (and this is the formulation used below) it is a single `G`-equivariant map

  `T : V_k ⊗ V_{j'} → V_j`,   `T (e_q ⊗ e_{m'}) = T^k_q e_{m'}`,

see `Phys.tensor_operator_covariance`, which derives the index form of the covariance law from
equivariance.

The Wigner–Eckart theorem states that, in the multiplicity-free situation (the space of
intertwiners `V_k ⊗ V_{j'} → V_j` being at most one-dimensional — for `SU(2)` this is the
multiplicity-one property of the Clebsch–Gordan series), all matrix elements of `T` factor as

  `⟨j m | T^k_q | j' m'⟩ = ⟨j ‖ T ‖ j'⟩ · C^{j m}_{k q ; j' m'}`,

where the Clebsch–Gordan coefficients `C` are the matrix elements of one fixed nonzero
intertwiner and the *reduced matrix element* `⟨j ‖ T ‖ j'⟩` is a single complex number,
independent of the magnetic quantum numbers `m, q, m'`.

`Phys.schur_rank_intertwiners_le_one` shows that the multiplicity-one hypothesis is exactly of
Schur type: it holds automatically whenever source and target are irreducible.
-/

namespace Phys

open Representation TensorProduct

section Intertwiners

variable {G V W : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The space of intertwiners (`G`-equivariant linear maps) between two representations,
as a `ℂ`-submodule of all linear maps. -/
def intertwiners (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Submodule ℂ (V →ₗ[ℂ] W) where
  carrier := {f | ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)}
  add_mem' {f₁ f₂} h₁ h₂ g v := by simp [h₁ g v, h₂ g v]
  zero_mem' g v := by simp
  smul_mem' c f h g v := by simp [h g v]

@[simp] lemma mem_intertwiners {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} : f ∈ intertwiners ρ σ ↔ ∀ (g : G) (v : V), f (ρ g v) = σ g (f v) := Iff.rfl

/-- Bundled form of a member of `Phys.intertwiners`. -/
def toIntertwiningMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} (hf : f ∈ intertwiners ρ σ) : IntertwiningMap ρ σ where
  toLinearMap := f
  isIntertwining' := hf

@[simp] lemma coe_toIntertwiningMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} (hf : f ∈ intertwiners ρ σ) :
    ⇑(toIntertwiningMap hf) = ⇑f := rfl

/-- **Multiplicity one implies proportionality.**  If the intertwiner space is at most
one-dimensional, then every intertwiner is a scalar multiple of a fixed nonzero one. -/
theorem intertwiner_eq_smul {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hmult : Module.rank ℂ (intertwiners ρ σ) ≤ 1)
    {C T : V →ₗ[ℂ] W} (hC : C ∈ intertwiners ρ σ) (hT : T ∈ intertwiners ρ σ) (hC0 : C ≠ 0) :
    ∃ r : ℂ, T = r • C := by
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hmult
  obtain ⟨a, ha⟩ := hv₀ ⟨C, hC⟩
  obtain ⟨b, hb⟩ := hv₀ ⟨T, hT⟩
  have ha' : a • (v₀ : V →ₗ[ℂ] W) = C := congrArg Subtype.val ha
  have hb' : b • (v₀ : V →ₗ[ℂ] W) = T := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha'
    exact hC0 ha'.symm
  exact ⟨b / a, by rw [← ha', ← hb', smul_smul, div_mul_cancel₀ _ ha0]⟩

end Intertwiners

section Schur

variable {G V W : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The inverse of a bijective intertwiner is an intertwiner. -/
theorem inv_mem_intertwiners {f : V →ₗ[ℂ] W} (hf : f ∈ intertwiners ρ σ)
    (hbij : Function.Bijective f) :
    (LinearEquiv.ofBijective f hbij).symm.toLinearMap ∈ intertwiners σ ρ := by
  intro g w
  apply hbij.injective
  have h1 : f ((LinearEquiv.ofBijective f hbij).symm (σ g w)) = σ g w :=
    (LinearEquiv.ofBijective f hbij).apply_symm_apply _
  have h2 : f (ρ g ((LinearEquiv.ofBijective f hbij).symm w)) =
      σ g (f ((LinearEquiv.ofBijective f hbij).symm w)) := hf _ _
  simp [h1, h2]

/-- **Schur's lemma.**  Between irreducible complex representations (the target being
finite-dimensional) the space of intertwiners has rank at most one.  This is what makes the
multiplicity-one hypothesis of `Phys.wigner_eckart` a Schur-type condition. -/
theorem schur_rank_intertwiners_le_one [ρ.IsIrreducible] [σ.IsIrreducible]
    [FiniteDimensional ℂ W] :
    Module.rank ℂ (intertwiners ρ σ) ≤ 1 := by
  rw [rank_le_one_iff]
  by_cases h0 : ∀ f : intertwiners ρ σ, f = 0
  · exact ⟨0, fun v => ⟨0, by rw [h0 v, smul_zero]⟩⟩
  push_neg at h0
  obtain ⟨f₀, hf₀⟩ := h0
  refine ⟨f₀, fun T => ?_⟩
  -- `f₀` is a nonzero intertwiner, hence bijective
  have hf₀' : (toIntertwiningMap f₀.2) ≠ 0 := by
    intro h
    apply hf₀
    ext v
    exact congrFun (congrArg (fun (u : IntertwiningMap ρ σ) => ⇑u) h) v
  have hbij : Function.Bijective (f₀ : V →ₗ[ℂ] W) := by
    rcases Representation.IsIrreducible.bijective_or_eq_zero (toIntertwiningMap f₀.2) with h | h
    · exact h
    · exact absurd h hf₀'
  -- transport `T` to an endomorphism of `σ`, which is a scalar by Schur over `ℂ`
  set e := LinearEquiv.ofBijective (f₀ : V →ₗ[ℂ] W) hbij with he
  have hinv : e.symm.toLinearMap ∈ intertwiners σ ρ := inv_mem_intertwiners f₀.2 hbij
  set E : IntertwiningMap σ σ :=
    (toIntertwiningMap T.2).comp (toIntertwiningMap hinv) with hE
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).2 E
  refine ⟨c, ?_⟩
  have hcE : ∀ w : W, c • (w : W) = E w := by
    intro w
    have := congrArg (fun (u : IntertwiningMap σ σ) => u w) hc
    simpa [IntertwiningMap.algebraMap_apply] using this
  ext v
  have hEv : E ((f₀ : V →ₗ[ℂ] W) v) = (T : V →ₗ[ℂ] W) v := by
    have : e.symm ((f₀ : V →ₗ[ℂ] W) v) = v := by
      simp [he]
    simp [hE, IntertwiningMap.comp, IntertwiningMap.llcomp, toIntertwiningMap, this]
  have := hcE ((f₀ : V →ₗ[ℂ] W) v)
  rw [hEv] at this
  simpa using this

end Schur

section TensorOperator

variable {G Vk Vj' Vj : Type*} [Monoid G]
  [AddCommGroup Vk] [Module ℂ Vk] [AddCommGroup Vj'] [Module ℂ Vj']
  [AddCommGroup Vj] [Module ℂ Vj]
  {ρk : Representation ℂ G Vk} {ρj' : Representation ℂ G Vj'} {ρj : Representation ℂ G Vj}

/-- **Tensor operator covariance.**  If `T : V_k ⊗ V_{j'} → V_j` is equivariant and we set
`T^k_q w := T (e_q ⊗ w)`, then the operators `T^k_q` obey the defining covariance law of a
rank-`k` tensor operator,
`U(g) T^k_q U(g)⁻¹ = ∑_{q'} D^k(g)_{q' q} T^k_{q'}`, written here in the equivalent form
`U(g) T^k_q w = ∑_{q'} D^k(g)_{q' q} T^k_{q'} (U(g) w)`. -/
theorem tensor_operator_covariance {ιk : Type*} [Fintype ιk] (bk : Module.Basis ιk ℂ Vk)
    {T : TensorProduct ℂ Vk Vj' →ₗ[ℂ] Vj} (hT : T ∈ intertwiners (ρk.tprod ρj') ρj)
    (g : G) (q : ιk) (w : Vj') :
    ρj g (T (bk q ⊗ₜ[ℂ] w)) =
      ∑ q' : ιk, bk.repr (ρk g (bk q)) q' • T (bk q' ⊗ₜ[ℂ] ρj' g w) := by
  have hstep : ρj g (T (bk q ⊗ₜ[ℂ] w)) = T (ρk g (bk q) ⊗ₜ[ℂ] ρj' g w) := by
    have := hT g (bk q ⊗ₜ[ℂ] w)
    simp only [Representation.tprod] at this
    exact this.symm
  have hexp : ρk g (bk q) = ∑ q' : ιk, bk.repr (ρk g (bk q)) q' • bk q' :=
    (bk.sum_repr _).symm
  rw [hstep]
  conv_lhs => rw [hexp]
  rw [TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]

/-- **The Wigner–Eckart theorem.**

Let `ρk`, `ρj'`, `ρj` be complex representations of a group `G` (the rank-`k` operator multiplet
and the initial and final state multiplets), with bases indexed by the magnetic quantum numbers
`q`, `m'`, `m`.  Assume multiplicity one, i.e. that the space of intertwiners
`V_k ⊗ V_{j'} → V_j` has rank at most one (for `SU(2)` this is the multiplicity-one property of
the Clebsch–Gordan series; in general it is a Schur-type condition, see
`Phys.schur_rank_intertwiners_le_one`).

Let `CG` be a fixed nonzero intertwiner — its matrix elements
`⟨j m | CG | k q ; j' m'⟩` are the Clebsch–Gordan coefficients — and let `T` be any tensor
operator, i.e. any intertwiner (see `Phys.tensor_operator_covariance`).

Then there is a single number `r` (the *reduced matrix element* `⟨j ‖ T ‖ j'⟩`), independent of
the magnetic quantum numbers `q, m', m`, such that every matrix element of `T` factorises as
Clebsch–Gordan coefficient times reduced matrix element. -/
theorem wigner_eckart {ιk ιj' ιj : Type*}
    (bk : Module.Basis ιk ℂ Vk) (bj' : Module.Basis ιj' ℂ Vj') (bj : Module.Basis ιj ℂ Vj)
    (hmult : Module.rank ℂ (intertwiners (ρk.tprod ρj') ρj) ≤ 1)
    {CG T : TensorProduct ℂ Vk Vj' →ₗ[ℂ] Vj}
    (hCG : CG ∈ intertwiners (ρk.tprod ρj') ρj)
    (hT : T ∈ intertwiners (ρk.tprod ρj') ρj)
    (hCG0 : CG ≠ 0) :
    ∃ r : ℂ, ∀ (q : ιk) (m' : ιj') (m : ιj),
      bj.repr (T (bk q ⊗ₜ[ℂ] bj' m')) m = r * bj.repr (CG (bk q ⊗ₜ[ℂ] bj' m')) m := by
  obtain ⟨r, hr⟩ := intertwiner_eq_smul hmult hCG hT hCG0
  refine ⟨r, fun q m' m => ?_⟩
  rw [hr]
  simp

/-- The hypotheses of `Phys.wigner_eckart` are satisfiable: for the scalar operator (`k = 0`)
between one-dimensional trivial multiplets, the intertwiner space has rank one and contains a
nonzero element (the multiplication map, playing the role of the Clebsch–Gordan intertwiner). -/
theorem wigner_eckart_hypotheses_nonvacuous (G : Type*) [Group G] :
    ∃ CG : TensorProduct ℂ ℂ ℂ →ₗ[ℂ] ℂ,
      CG ∈ intertwiners ((Representation.trivial ℂ G ℂ).tprod (Representation.trivial ℂ G ℂ))
          (Representation.trivial ℂ G ℂ) ∧ CG ≠ 0 ∧
        Module.rank ℂ (intertwiners
            ((Representation.trivial ℂ G ℂ).tprod (Representation.trivial ℂ G ℂ))
            (Representation.trivial ℂ G ℂ)) ≤ 1 := by
  have htop : intertwiners ((Representation.trivial ℂ G ℂ).tprod (Representation.trivial ℂ G ℂ))
      (Representation.trivial ℂ G ℂ) = ⊤ := by
    ext f
    simp [intertwiners, Representation.tprod, Representation.trivial]
  refine ⟨(TensorProduct.lid ℂ ℂ).toLinearMap, by rw [htop]; trivial, ?_, ?_⟩
  · intro h
    have : (TensorProduct.lid ℂ ℂ) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 :=
      congrFun (congrArg DFunLike.coe h) _
    simp at this
  · rw [htop, rank_top]
    have h1 : Module.finrank ℂ (TensorProduct ℂ ℂ ℂ →ₗ[ℂ] ℂ) = 1 := by
      rw [Module.finrank_linearMap, Module.finrank_tensorProduct]; simp
    rw [← Module.finrank_eq_rank, h1]
    norm_cast

end TensorOperator

end Phys

#print axioms Phys.wigner_eckart
#print axioms Phys.schur_rank_intertwiners_le_one
#print axioms Phys.tensor_operator_covariance
#print axioms Phys.wigner_eckart_hypotheses_nonvacuous

