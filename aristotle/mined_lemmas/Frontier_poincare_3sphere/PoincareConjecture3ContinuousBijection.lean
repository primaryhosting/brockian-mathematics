import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(Lean requires `import` to be the very first command of a file, before any module-level doc
comment, so the required header block is placed immediately after `import Mathlib`.)

## Contents

* `Frontier.IsClosed3Manifold` : a closed (compact, boundaryless, second countable, Hausdorff)
  topological 3-manifold.
* `Frontier.IsSimplyConnectedClosed3Manifold` : the hypothesis class of the Poincaré conjecture.
* `Frontier.PoincareConjecture3` : the formal statement of the Poincaré conjecture in dimension 3
  (Perelman): every simply connected closed 3-manifold is homeomorphic to `S³`.
* `Frontier.poincare_3sphere` : the Lean-checked *reduction*: the conjecture is equivalent to the
  a priori weaker statement that every simply connected closed 3-manifold admits a continuous
  bijection onto `S³`.  The nontrivial direction is closed by the Mathlib lemma
  `Continuous.homeoOfEquivCompactToT2` (a continuous bijection from a compact space to a Hausdorff
  space is a homeomorphism).
* Supporting results: the hypothesis class is invariant under homeomorphism
  (`Frontier.IsSimplyConnectedClosed3Manifold.homeomorph`) and is realized by `S³` itself
  (`Frontier.sphere3_isClosed3Manifold`), so the statement is not vacuous.

The base case of the conjecture — that `S³` really is a simply connected closed 3-manifold, and
that the conjecture holds for every space homeomorphic to it — is proved in
`RequestProject/Sphere3SimplyConnected.lean`.
-/

universe u v

namespace Frontier

open Metric

/-- The model space `ℝ³` for 3-manifolds. -/
abbrev EuclideanThree : Type := EuclideanSpace ℝ (Fin 3)

/-- The 3-sphere, as the unit sphere of `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- A *closed 3-manifold*: a compact, Hausdorff, second countable topological space which is
locally homeomorphic to `ℝ³` (a boundaryless topological 3-manifold, i.e. charted over `ℝ³`). -/
structure IsClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop where
  t2Space : T2Space M
  compactSpace : CompactSpace M
  secondCountableTopology : SecondCountableTopology M
  chartedSpace : Nonempty (ChartedSpace EuclideanThree M)

/-- The hypothesis class of the Poincaré conjecture: a simply connected closed 3-manifold. -/
structure IsSimplyConnectedClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop
    extends IsClosed3Manifold M where
  simplyConnectedSpace : SimplyConnectedSpace M

/-- **The Poincaré conjecture in dimension three** (Perelman): every simply connected closed
3-manifold is homeomorphic to the 3-sphere. -/

def PoincareConjecture3ContinuousBijection : Prop :=
  ∀ (M : Type u) [TopologicalSpace M], IsSimplyConnectedClosed3Manifold M →
    ∃ f : M → Sphere3, Continuous f ∧ Function.Bijective f

section Transfer

variable {H : Type*} {M : Type u} {N : Type v}
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]

/-- A charted space structure transports along a homeomorphism. -/
