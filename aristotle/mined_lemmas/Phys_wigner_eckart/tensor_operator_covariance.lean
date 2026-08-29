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
