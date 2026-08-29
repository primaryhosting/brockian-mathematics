/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain comment
-- and is repeated below as the module docstring.)

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

`E4` is the standard model space `ℝ⁴` (as a Euclidean space), and `Smooth4Manifold`
bundles a smooth (`C^∞`) manifold modelled on `ℝ⁴`: a carrier type together with its
topology, an atlas of charts into `ℝ⁴`, and the smoothness condition on the transition maps.
-/

/-- The model space `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- A smooth (`C^∞`) manifold modelled on `ℝ⁴`, bundled with all of its structure. -/
structure Smooth4Manifold where
  /-- The underlying set of points of the manifold. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace E4 carrier]
  [manifold : IsManifold (𝓘(ℝ, E4)) ∞ carrier]

attribute [instance] Smooth4Manifold.topology Smooth4Manifold.charted Smooth4Manifold.manifold

/-- Two smooth `4`-manifolds are *diffeomorphic* when there is a `C^∞` diffeomorphism
between them. -/

theorem homeoR4_standardR4 : HomeoR4 standardR4 := ⟨Homeomorph.refl _⟩

/-- Anything diffeomorphic to a manifold homeomorphic to `ℝ⁴` is itself homeomorphic
to `ℝ⁴`. -/
