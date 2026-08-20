import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Filter Set Topology
open scoped ENNReal

namespace Frontier

/-! ## Setup

Uhlenbeck's compactness theorem for Yang–Mills connections asserts that a sequence of
connections with uniformly bounded Yang–Mills energy converges (after gauge transformations
and passing to a subsequence) away from a *finite* set of points, the *bubbling points*,
at which a definite quantum of energy concentrates.

The quantitative combinatorial heart of that statement — the part that is independent of
gauge theory and is what actually produces the finiteness of the bubbling set — is the
following: if `ν i` is the sequence of energy measures, uniformly bounded by `E`, then the
set of points at which at least `ε₀` of energy concentrates in every ball is finite, of
cardinality at most `E / ε₀`.  (The gauge-theoretic input, `ε`-regularity, is what
guarantees that away from this set the connections converge; it is not formalized here.)

We formalize this statement and prove it. -/

/-- The *energy measure* attached to a curvature field `F` on a measure space `(X, μ)`:
the measure with density `‖F x‖ ^ 2` with respect to `μ`.  For a Yang–Mills connection `A`
on `ℝ⁴` with curvature `F_A`, this is the measure `|F_A|² dvol` whose total mass is the
Yang–Mills energy. -/

def bubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (ν : ℕ → Measure X) (ε₀ : ℝ≥0∞) : Set X :=
  {x | ∀ r : ℝ, 0 < r → ε₀ ≤ liminf (fun i => ν i (ball x r)) atTop}

/-! ## Auxiliary lemmas -/

/-- A finite set of points in a metric space can be surrounded by pairwise disjoint balls
of a common positive radius. -/
