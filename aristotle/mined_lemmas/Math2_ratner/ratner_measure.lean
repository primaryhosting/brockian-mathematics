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

theorem ratner_measure {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] [MeasurableSpace (G ⧸ N)] [BorelSpace (G ⧸ N)]
    [T2Space (G ⧸ N)] [CompactSpace (G ⧸ N)]
    (u : ℝ → G) (hu : Continuous u) (hmul : ∀ s t : ℝ, u (s + t) = u s * u t) (x : G ⧸ N) :
    ∃ H : Subgroup (G ⧸ N),
      IsClosed (H : Set (G ⧸ N)) ∧
      IsConnected (H : Set (G ⧸ N)) ∧
      (∀ t : ℝ, (QuotientGroup.mk (u t) : G ⧸ N) ∈ H) ∧
      closure (Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x)
        = (fun g => g * x) '' (H : Set (G ⧸ N)) ∧
      ∃ μ : MeasureTheory.Measure (G ⧸ N), MeasureTheory.IsProbabilityMeasure μ ∧
        μ (closure (Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x)) = 1 ∧
        ∀ t : ℝ, MeasureTheory.Measure.map
          (fun y => (QuotientGroup.mk (u t) : G ⧸ N) * y) μ = μ := by
  obtain ⟨H, hHclosed, hHconn, hHmem, hHorbit⟩ := ratner N u hu hmul x
  obtain ⟨μ, hμprob, hμmass, hμinv⟩ :=
    homogeneous_measure_of_isCompact H (hHclosed.isCompact) x
  exact ⟨H, hHclosed, hHconn, hHmem, hHorbit,
    μ, hμprob, by rw [hHorbit]; exact hμmass, fun t => hμinv _ (hHmem t)⟩

/-- Non-vacuity of `Math2.ratner_measure`: the hypotheses are satisfied by the linear flow on the
circle `ℝ / ℤ`, whose orbit closure is the whole circle carrying its Haar probability measure. -/
