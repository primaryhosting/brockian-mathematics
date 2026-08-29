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
