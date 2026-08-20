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

theorem isExoticR4_of_diffeomorph {M N : SmoothManifold4}
    (e : N.carrier ≃ₘ⟮𝓡 4, 𝓡 4⟯ M.carrier) (hM : IsExoticR4 M) : IsExoticR4 N := by
  obtain ⟨⟨f⟩, hd⟩ := hM
  refine ⟨⟨e.toHomeomorph.trans f⟩, ⟨fun g => hd.elim (e.symm.trans g)⟩⟩

/-- **Reduction to a smooth invariant.** To exhibit an exotic `ℝ⁴` it suffices to produce a
smooth `4`-manifold `M` homeomorphic to `ℝ⁴` together with a diffeomorphism-invariant property
`P` which holds for the standard `ℝ⁴` but fails for `M`. This is exactly the shape of the
Donaldson-invariant / gauge-theoretic argument. -/
