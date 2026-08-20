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

theorem isExoticR4_of_invariant (P : SmoothManifold4 → Prop)
    (hP : ∀ A B : SmoothManifold4, (A.carrier ≃ₘ⟮𝓡 4, 𝓡 4⟯ B.carrier) → P A → P B)
    (M : SmoothManifold4) (hhomeo : Nonempty (M.carrier ≃ₜ EuclideanR4))
    (hstd : P standardR4) (hM : ¬ P M) : IsExoticR4 M :=
  ⟨hhomeo, ⟨fun e => hM (hP standardR4 M e.symm hstd)⟩⟩

/-- **A homeomorphic copy of `ℝ⁴` with the transported smooth structure is never exotic.**
If `X` is any topological space homeomorphic to `ℝ⁴` and we give `X` the smooth structure
whose single chart is that homeomorphism, then `X` is diffeomorphic to `ℝ⁴`. Hence an exotic
`ℝ⁴` can never be obtained by merely transporting the standard structure along a
homeomorphism: it must come from a genuinely incompatible atlas. -/
