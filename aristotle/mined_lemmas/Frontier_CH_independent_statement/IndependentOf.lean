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

def IndependentOf {L : Language} (T : L.Theory) (σ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ σ ∧ ¬ T ⊨ᵇ σ.not

section Independence

variable {L : Language} {T : L.Theory} {σ : L.Sentence}

/-- Adding a doubly negated sentence to a theory is, for satisfiability purposes, the same as
adding the sentence itself. -/
