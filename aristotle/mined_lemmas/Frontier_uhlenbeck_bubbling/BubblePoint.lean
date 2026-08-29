import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Metric Set

/-- A point `x` is an *energy concentration point* (a *bubble point*) at level `eps`
for a sequence of energy measures `mu n` (think: `mu n = |F_{A n}|² dvol`, the Yang–Mills
energy density of a sequence of connections `A n`) if on *every* ball around `x` the
asymptotic energy is at least `eps`. -/

def BubblePoint {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : ℕ → Measure X) (eps : ℝ≥0∞) (x : X) : Prop :=
  ∀ r : ℝ, 0 < r → eps ≤ liminf (fun n => mu n (Metric.ball x r)) atTop

/-- The set of bubble points ("blow-up set") of a sequence of energy measures. -/
