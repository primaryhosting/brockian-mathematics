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

theorem ratner_orbitClosureProperty {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] (u : ℝ → G) (hu : Continuous u)
    (hmul : ∀ s t : ℝ, u (s + t) = u s * u t) : RatnerOrbitClosureProperty N u := by
  intro x
  obtain ⟨H', hclosed, _, hmem, horb⟩ := ratner N u hu hmul x
  have hsmul : ∀ (g : G) (y : G ⧸ N), g • y = (QuotientGroup.mk g : G ⧸ N) * y := by
    intro g y
    induction y using QuotientGroup.induction_on
    rfl
  refine ⟨H'.comap (QuotientGroup.mk' N), ?_, fun t => hmem t, ?_⟩
  · rw [Subgroup.coe_comap]
    exact hclosed.preimage continuous_quot_mk
  · have h1 : (Set.range fun t : ℝ => u t • x)
        = Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x := by
      simp only [hsmul]
    have hmapcomap := congrArg (fun K : Subgroup (G ⧸ N) => (K : Set (G ⧸ N)))
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) H')
    simp only [Subgroup.coe_map] at hmapcomap
    have h2 : (fun h : G => h • x) '' ((H'.comap (QuotientGroup.mk' N) : Subgroup G) : Set G)
        = (fun g => g * x) '' (H' : Set (G ⧸ N)) := by
      rw [← hmapcomap, Set.image_image]
      simp only [hsmul]
      rfl
    rw [h1, horb, h2]

/-! ## Homogeneous invariant measures -/

/-- A compact subgroup `H` of a topological group carries a Haar probability measure; pushing it
forward to the coset `H * x` produces an `H`-invariant probability measure concentrated on that
coset (the *homogeneous measure* of the coset). -/
@[to_additive homogeneous_measure_of_isCompact_add]
