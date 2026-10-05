/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped Manifold ContDiff
open Metric (sphere)

namespace Frontier

/-- `ℝ³`, the Euclidean model space of dimension `3`. -/
abbrev EuclideanThree : Type := EuclideanSpace ℝ (Fin 3)

/-- The standard `3`-sphere `𝕊³ ⊆ ℝ⁴`. -/
abbrev ThreeSphere : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `ℝ⁴` is `4 = 3 + 1`-dimensional; this is what equips `𝕊³` with its charts. -/
instance factFinrankFour : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- **The 3-dimensional topological Poincaré conjecture** (Perelman):
every simply-connected closed (compact, boundaryless) topological `3`-manifold is
homeomorphic to the `3`-sphere.  Here "closed `3`-manifold" is spelled as in Mathlib:
a compact Hausdorff space charted on `ℝ³`. -/

def PoincareConjecture3Bijection : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
    ∃ f : M → ThreeSphere, Continuous f ∧ Function.Bijective f

/-- An even weaker looking form of the conjecture: only a *continuous injection with dense
range* into `𝕊³` is required. -/
