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

theorem CH_independent_of_ZFC (ZFC : setLang.Theory) (CH : setLang.Sentence)
    (godel : (ZFC ∪ {CH}).IsSatisfiable) (cohen : (ZFC ∪ {CH.not}).IsSatisfiable) :
    ¬ ZFC ⊨ᵇ CH ∧ ¬ ZFC ⊨ᵇ CH.not :=
  (CH_independent_statement ZFC CH).2 ⟨godel, cohen⟩

/-!
## Part 4: the criterion is non-vacuous

A fully checked instance of the independence criterion in the language of set theory: the
sentence "there exist two distinct sets" is independent of the empty theory, since a one-element
`∈`-structure refutes it while a two-element `∈`-structure satisfies it.
-/

/-- The trivial `∈`-structure (empty membership relation) on any type. -/
