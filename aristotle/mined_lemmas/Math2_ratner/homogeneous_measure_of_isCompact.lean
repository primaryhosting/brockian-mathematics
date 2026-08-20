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

theorem homogeneous_measure_of_isCompact [MeasurableSpace Q] [BorelSpace Q] [T2Space Q]
    (H : Subgroup Q) (hcomp : IsCompact (H : Set Q)) (x : Q) :
    ∃ μ : MeasureTheory.Measure Q, MeasureTheory.IsProbabilityMeasure μ ∧
      μ ((fun g => g * x) '' (H : Set Q)) = 1 ∧
      ∀ h ∈ H, MeasureTheory.Measure.map (fun y => h * y) μ = μ := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hcomp
  set ν : MeasureTheory.Measure H := MeasureTheory.Measure.haarMeasure ⊤
  haveI : MeasureTheory.IsProbabilityMeasure ν := by
    constructor
    simpa using MeasureTheory.Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
  set φ : H → Q := fun h => (h : Q) * x with hφ
  have hφm : Measurable φ := (by fun_prop : Continuous φ).measurable
  refine ⟨ν.map φ, MeasureTheory.Measure.isProbabilityMeasure_map hφm.aemeasurable, ?_, ?_⟩
  · have hs : MeasurableSet ((fun g => g * x) '' (H : Set Q)) :=
      (hcomp.image (by fun_prop)).isClosed.measurableSet
    rw [MeasureTheory.Measure.map_apply hφm hs]
    have hpre : φ ⁻¹' ((fun g => g * x) '' (H : Set Q)) = Set.univ := by
      ext h; simp [hφ]
    rw [hpre]
    simp
  · intro h hh
    have hmulm : Measurable (fun y : Q => h * y) := (continuous_mul_left h).measurable
    rw [MeasureTheory.Measure.map_map hmulm hφm]
    have hcomp' : ((fun y : Q => h * y) ∘ φ) = φ ∘ (fun k : H => (⟨h, hh⟩ : H) * k) := by
      funext k; simp [hφ, mul_assoc]
    rw [hcomp', ← MeasureTheory.Measure.map_map hφm (measurable_const_mul _)]
    congr 1
    exact MeasureTheory.map_mul_left_eq_self ν (⟨h, hh⟩ : H)

/-- **Ratner's theorems, orbit closure together with its homogeneous invariant measure**, in the
setting of a compact quotient `G ⧸ N` of a topological group by a normal subgroup.

For a continuous one-parameter subgroup `u` and any point `x`, the orbit closure is a translate
`H · x` of a closed connected subgroup `H` containing the flow, and it carries a flow-invariant
probability measure of full mass on it, namely the homogeneous (Haar) measure of `H · x`. -/
@[to_additive ratner_add_measure]
