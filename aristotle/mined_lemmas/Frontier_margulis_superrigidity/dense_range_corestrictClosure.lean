import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

universe u

/-! ## The conclusion of superrigidity -/

/-- The conclusion of Margulis superrigidity for a homomorphism `ρ : Γ →* H` defined on a
subgroup `Γ` of a topological group `G`: `ρ` is the restriction of a continuous homomorphism
`G →* H`. -/

theorem dense_range_corestrictClosure {Γ : Subgroup G} (ρ : Γ →* H) :
    Dense (Set.range (corestrictClosure ρ)) := by
  rw [(IsEmbedding.subtypeVal (p := fun x : H => x ∈ (MonoidHom.range ρ).topologicalClosure)).isInducing.dense_iff]
  rintro ⟨x, hx⟩
  have himg : Subtype.val '' (Set.range (corestrictClosure ρ)) = Set.range ρ := by
    ext y
    constructor
    · rintro ⟨-, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨corestrictClosure ρ γ, ⟨γ, rfl⟩, rfl⟩
  rw [himg]
  have : ((MonoidHom.range ρ).topologicalClosure : Set H) = closure (Set.range ρ) := by
    simp [Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  rw [this] at hx
  exact hx

/-- **Local reduction to the dense-image case.** If the corestriction of `ρ` to the closure of its
image extends to a continuous homomorphism, then so does `ρ` itself. -/
