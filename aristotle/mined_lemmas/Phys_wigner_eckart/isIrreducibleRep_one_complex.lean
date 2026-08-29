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
