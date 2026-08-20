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

theorem dense_image_add_right {X : Type*} [TopologicalSpace X] [AddGroup X]
    [IsTopologicalAddGroup X] {s : Set X} (hs : Dense s) (x : X) :
    Dense ((fun g => g + x) '' s) := by
  have h := (Homeomorph.addRight x).image_closure s
  rw [dense_iff_closure_eq] at hs ⊢
  simp only [Homeomorph.coe_addRight] at h
  rw [← h, hs]
  exact Set.image_univ_of_surjective fun y => ⟨y - x, by simp⟩

/-- The linear flow of irrational slope `a` on the `2`-torus has dense orbits: the subgroup
`H` produced by Ratner's theorem is all of `ℝ² / ℤ²`. This is Kronecker's theorem, the abelian
instance of Ratner's minimality statement for unipotent flows. -/
