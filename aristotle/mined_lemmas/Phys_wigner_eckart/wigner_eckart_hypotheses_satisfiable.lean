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

