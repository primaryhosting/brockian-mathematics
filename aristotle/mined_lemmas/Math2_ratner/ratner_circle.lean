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

theorem ratner_circle (x : AddCircle (1 : ℝ)) :
    ∃ H : AddSubgroup (AddCircle (1 : ℝ)),
      IsClosed (H : Set (AddCircle (1 : ℝ))) ∧
      IsConnected (H : Set (AddCircle (1 : ℝ))) ∧
      (∀ t : ℝ, (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) ∈ H) ∧
      closure (Set.range fun t : ℝ => (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) + x)
        = (fun g => g + x) '' (H : Set (AddCircle (1 : ℝ))) ∧
      ∃ μ : MeasureTheory.Measure (AddCircle (1 : ℝ)),
        MeasureTheory.IsProbabilityMeasure μ ∧
        μ (closure (Set.range fun t : ℝ =>
          (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) + x)) = 1 ∧
        ∀ t : ℝ, MeasureTheory.Measure.map
          (fun y => (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) + y) μ = μ :=
  ratner_add_measure _ (fun t => t) continuous_id (fun _ _ => rfl) x

/-! ## The classical case: linear flows on the torus `ℝⁿ / ℤⁿ` -/

/-- The standard lattice `ℤⁿ ≤ ℝⁿ`. -/
