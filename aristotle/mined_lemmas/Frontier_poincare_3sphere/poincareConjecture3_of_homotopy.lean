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

theorem poincareConjecture3_of_homotopy
    (h₁ : HomotopyPoincare3) (h₂ : GeneralizedPoincare3) : PoincareConjecture3 := by
  intro M _ _ _ _ _
  exact h₂ M (h₁ M).some

/-- The class of simply-connected closed `3`-manifolds is invariant under homeomorphism:
if `N` is homeomorphic to such a manifold `M`, then `N` is one as well.  Hence the conjecture
only has to be checked on one representative of each homeomorphism class. -/
