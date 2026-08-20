import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Pointwise Topology

namespace Math2

/-! ## Closures of coset-orbits are cosets -/

variable {Q : Type*} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]

/-- The closure of the orbit `S * x` of a subgroup `S` is the coset `S̄ * x`
of the topological closure of `S`. -/
@[to_additive closure_addCoset_eq /-- The closure of the orbit `S + x` of an additive subgroup `S`
is the coset `S̄ + x` of the topological closure of `S`. -/]

def RatnerOrbitClosureProperty {G : Type*} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) (u : ℝ → G) : Prop :=
  ∀ x : G ⧸ Γ, ∃ H : Subgroup G, IsClosed (H : Set G) ∧ (∀ t : ℝ, u t ∈ H) ∧
    closure (Set.range fun t : ℝ => u t • x) = (fun h : G => h • x) '' (H : Set G)

/-- Ratner's orbit closure property holds for every continuous one-parameter subgroup acting on
`G ⧸ N` with `N` a normal subgroup. -/
