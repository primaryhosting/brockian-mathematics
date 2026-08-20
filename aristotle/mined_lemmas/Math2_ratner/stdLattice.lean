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

def stdLattice (n : ℕ) : AddSubgroup (Fin n → ℝ) :=
  AddSubgroup.closure (Set.range fun i : Fin n => Pi.single i (1 : ℝ))

/-- The `n`-dimensional torus `ℝⁿ / ℤⁿ`. -/
abbrev Torus (n : ℕ) := (Fin n → ℝ) ⧸ stdLattice n

/-- **Ratner's orbit closure theorem for linear flows on the torus `ℝⁿ / ℤⁿ`.**
The closure of the orbit of the linear flow `t ↦ x + t • v` is the translate by `x` of a closed
connected subgroup (a subtorus) of `ℝⁿ / ℤⁿ` containing the flow direction. -/
