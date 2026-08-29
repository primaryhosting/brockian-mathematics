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

