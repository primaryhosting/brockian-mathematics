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

theorem range_invariant {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} (hf : Intertwines ρ σ f) (g : G) (w : W)
    (hw : w ∈ LinearMap.range f) : σ g w ∈ LinearMap.range f := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨ρ g v, hf g v⟩

/-- **Schur's lemma**, first part: a nonzero intertwiner between irreducible
representations is bijective. -/
