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

def IsLatticeIn {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) (Γ : Subgroup G) : Prop :=
  DiscreteTopology Γ ∧
    ∃ F : Set G, MeasureTheory.IsFundamentalDomain Γ.op F μ ∧ μ F ≠ ⊤

/-- `IsIrreducibleLattice Γ` says that the lattice `Γ ≤ G` is irreducible: `Γ` together with any
proper closed normal subgroup of `G` generates a dense subgroup (equivalently, the image of `Γ`
in every proper quotient of `G` by a closed normal subgroup is dense). -/
