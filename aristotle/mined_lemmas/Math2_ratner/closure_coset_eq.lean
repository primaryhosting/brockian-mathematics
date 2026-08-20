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

theorem closure_coset_eq (S : Subgroup Q) (x : Q) :
    closure ((fun g => g * x) '' (S : Set Q))
      = (fun g => g * x) '' (S.topologicalClosure : Set Q) := by
  have h := (Homeomorph.mulRight x).image_closure (S : Set Q)
  simpa [Subgroup.topologicalClosure_coe] using h.symm

/-! ## Orbit closures of one-parameter subgroups -/

/-- The closure of the orbit `{f t * x : t ∈ ℝ}` of a continuous one-parameter subgroup `f` of a
topological group `Q` is the translate `H * x` of a closed connected subgroup `H` containing the
image of `f`. -/
@[to_additive oneParamAddOrbitClosure /-- The closure of the orbit `{f t + x : t ∈ ℝ}` of a
continuous one-parameter subgroup `f` of a topological additive group `Q` is the translate
`H + x` of a closed connected subgroup `H` containing the image of `f`. -/]
