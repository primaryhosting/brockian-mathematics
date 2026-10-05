import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Part 1: the Continuum Hypothesis inside Lean's own set theory
-/

open Cardinal

/-- The Continuum Hypothesis, phrased about sets of real numbers:
every infinite set of reals is either countable or of the cardinality of the continuum. -/

theorem continuumHypothesis_iff_no_intermediate_cardinal :
    ContinuumHypothesis ↔ ∀ c : Cardinal.{0}, ℵ₀ < c → c < 𝔠 → False := by
  rw [continuumHypothesis_iff_aleph_one_eq_continuum]
  constructor
  · intro h c h1 h2
    have h3 : (ℵ₁ : Cardinal.{0}) ≤ c := by
      rw [← Cardinal.succ_aleph0]; exact Order.succ_le_of_lt h1
    rw [h] at h3
    exact absurd (lt_of_le_of_lt h3 h2) (lt_irrefl _)
  · intro h
    refine le_antisymm Cardinal.aleph_one_le_continuum ?_
    by_contra hlt
    push_neg at hlt
    exact absurd (h _ Cardinal.aleph0_lt_aleph_one hlt) not_false

/-!
## Part 2: independence in first-order logic
-/

open FirstOrder Language

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
