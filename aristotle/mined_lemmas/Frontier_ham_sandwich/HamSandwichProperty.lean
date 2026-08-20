import Mathlib

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

/-!
# Ham–Sandwich: statement and the one-dimensional base case

The Ham–Sandwich theorem states that any `n` finite (Borel) measures on `ℝⁿ` can be
simultaneously bisected by a single affine hyperplane.  Here "bisected by the hyperplane
`{x | ⟪v, x⟫ = c}`" is taken in the usual measure-theoretic sense, which is the correct
formulation for measures that may have atoms: each of the two *open* half-spaces carries at
most half of the total mass (equivalently, each *closed* half-space carries at least half).

This file gives the formal statement `HamSandwichProperty n` in arbitrary dimension and a
complete, axiom-clean proof of the base case `n = 1` (`Frontier.ham_sandwich`), where the
hyperplane is a point and bisection is the existence of a median.
-/

namespace Frontier

open MeasureTheory Set Filter

/-- The hyperplane `{x | ⟪v, x⟫ = c}` bisects the measure `μ`: both open half-spaces
determined by it carry at most half of the total mass of `μ`. -/

def HamSandwichProperty (n : ℕ) : Prop :=
  ∀ μ : Fin n → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
    (∀ i, MeasureTheory.IsFiniteMeasure (μ i)) →
      ∃ v : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, v ≠ 0 ∧ ∀ i, BisectedBy (μ i) v c

/-- Every finite Borel measure on `ℝ` has a median: a point `c` such that both `Iio c` and
`Ioi c` carry at most half of the total mass. -/
