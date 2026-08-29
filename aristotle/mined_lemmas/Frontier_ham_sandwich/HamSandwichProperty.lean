/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-!
## Step 1: existence of a median for a finite measure on `ℝ`

A *median* of a finite measure `ν` on `ℝ` is a point `c` such that both closed half-lines
`Iic c` and `Ici c` carry at least half of the total mass.  This is the one-dimensional
form of "bisection by a hyperplane"; it is obtained by taking `c` to be the infimum of the
set of points where the cumulative distribution function has reached half of the total mass.
-/

/-- **Existence of a median.**  Every finite measure `ν` on `ℝ` admits a point `c` such that
each of the two closed half-lines determined by `c` carries at least half of the total mass. -/

def HamSandwichProperty (n : ℕ) : Prop :=
  ∀ μ : Fin n → Measure (EuclideanSpace ℝ (Fin n)), (∀ i, IsFiniteMeasure (μ i)) →
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), v ≠ 0 ∧ ∀ i,
      (μ i) Set.univ ≤ 2 * (μ i) {x | inner ℝ v x ≤ c} ∧
      (μ i) Set.univ ≤ 2 * (μ i) {x | c ≤ inner ℝ v x}

/-- **Ham–Sandwich theorem, base case `n = 1`.**  A single finite measure on `ℝ¹` can be
bisected by a hyperplane (i.e. a point): there is `v ≠ 0` and `c : ℝ` so that both closed
half-spaces `{x | ⟪v, x⟫ ≤ c}` and `{x | c ≤ ⟪v, x⟫}` carry at least half of the total mass. -/
