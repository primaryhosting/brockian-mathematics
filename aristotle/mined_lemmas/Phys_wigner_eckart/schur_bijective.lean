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
