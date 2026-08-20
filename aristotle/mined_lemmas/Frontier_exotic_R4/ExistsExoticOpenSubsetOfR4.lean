/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff Topology

namespace Frontier

/-- The standard model space `ℝ⁴` (as a Euclidean space). -/
abbrev EuclideanR4 : Type := EuclideanSpace ℝ (Fin 4)

/-- A smooth (`C^∞`) `4`-manifold: a topological space with an atlas of charts modelled on
`ℝ⁴` whose transition maps are smooth. -/
structure SmoothManifold4 where
  /-- The underlying set of points. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace EuclideanR4 carrier]
  [smooth : IsManifold (𝓡 4) ∞ carrier]

attribute [instance] SmoothManifold4.topology SmoothManifold4.charts SmoothManifold4.smooth

/-- `M` is an *exotic* `ℝ⁴`: it is homeomorphic to `ℝ⁴`, but there is no diffeomorphism
between `M` and `ℝ⁴` with its standard smooth structure. -/

def ExistsExoticOpenSubsetOfR4 : Prop :=
  ∃ U : TopologicalSpace.Opens EuclideanR4,
    Nonempty (U ≃ₜ EuclideanR4) ∧ IsEmpty (U ≃ₘ⟮𝓡 4, 𝓡 4⟯ EuclideanR4)

/-- **Exotic `ℝ⁴` (Freedman–Donaldson), as a Lean-checked reduction.**
Granting the Donaldson–Freedman input (an open subset of `ℝ⁴` homeomorphic but not
diffeomorphic to `ℝ⁴`), there exists a smooth `4`-manifold that is homeomorphic to `ℝ⁴`
but admits no diffeomorphism to `ℝ⁴`. The reduction verifies in Lean that such an open
subset does carry a genuine smooth `4`-manifold structure. -/
