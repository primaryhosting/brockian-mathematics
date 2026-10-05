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

theorem independentOf_iff_isSatisfiable :
    IndependentOf T σ ↔ (T ∪ {σ}).IsSatisfiable ∧ (T ∪ {σ.not}).IsSatisfiable := by
  rw [IndependentOf, Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable,
    not_not, not_not, isSatisfiable_union_not_not_iff]
  exact and_comm

/-- If both `T + σ` and `T + ¬σ` have models, then `σ` is independent of `T`. -/
