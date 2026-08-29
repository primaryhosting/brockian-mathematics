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

def MargulisSuperrigidityDenseImage : Prop :=
  ∀ {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] (Γ : Subgroup G) (ρ : Γ →* H),
    IsHigherRank G → IsLatticeIn μ Γ → IsIrreducibleLattice Γ →
    Dense (Set.range ρ) → ExtendsContinuously Γ ρ

/-! ## Elementary facts about the superrigidity conclusion -/

section Basic

variable {G H K : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K]

/-- Superrigidity is preserved by postcomposition with a continuous homomorphism. -/
