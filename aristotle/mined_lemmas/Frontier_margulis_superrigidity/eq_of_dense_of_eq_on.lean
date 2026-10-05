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

theorem eq_of_dense_of_eq_on [T2Space H] {Γ : Subgroup G} (hΓ : Dense (Γ : Set G))
    {σ τ : G →* H} (hσ : Continuous σ) (hτ : Continuous τ)
    (h : ∀ γ : Γ, σ (γ : G) = τ (γ : G)) : σ = τ := by
  ext g
  refine congrFun (Continuous.ext_on hΓ hσ hτ ?_) g
  rintro x hx
  exact h ⟨x, hx⟩

end Basic

/-! ## Base cases -/

section BaseCases

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- **Base case: rank zero / discrete ambient group.** If `G` carries the discrete topology, then
every homomorphism defined on all of `G` extends continuously (by itself). -/
