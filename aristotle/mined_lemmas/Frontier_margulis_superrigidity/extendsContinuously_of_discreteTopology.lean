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

theorem extendsContinuously_of_discreteTopology [DiscreteTopology G]
    (ρ : (⊤ : Subgroup G) →* H) : ExtendsContinuously (⊤ : Subgroup G) ρ := by
  refine ⟨ρ.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, continuous_of_discreteTopology,
    fun γ => ?_⟩
  simp [Subgroup.topEquiv]

/-- **Base case: abelian torsion-free targets.** A higher-rank lattice has property (T) and hence
finite abelianization; granting this (as the hypothesis `hab`), every homomorphism from `Γ` to a
torsion-free abelian topological group is trivial, and so extends continuously (by the trivial
homomorphism). -/
