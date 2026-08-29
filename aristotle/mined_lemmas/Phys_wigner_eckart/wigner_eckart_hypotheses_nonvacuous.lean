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

