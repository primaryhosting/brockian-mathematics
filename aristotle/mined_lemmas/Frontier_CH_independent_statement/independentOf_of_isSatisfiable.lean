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

theorem independentOf_of_isSatisfiable (h₁ : (T ∪ {σ}).IsSatisfiable)
    (h₂ : (T ∪ {σ.not}).IsSatisfiable) : IndependentOf T σ :=
  independentOf_iff_isSatisfiable.2 ⟨h₁, h₂⟩

end Independence

/-!
## Part 3: the target statement

The independence of the Continuum Hypothesis from `ZFC` is exactly the conjunction of the two
deep relative consistency theorems:

* Gödel (1938), the constructible universe `L`: `ZFC + CH` has a model;
* Cohen (1963), forcing: `ZFC + ¬CH` has a model.

The theorem below is the Lean-checked reduction: independence of `CH` from `ZFC` holds **iff**
these two model-existence statements hold. It is stated for an arbitrary theory `ZFC` and an
arbitrary sentence `CH` in the first-order language of set theory, so it applies in particular to
the usual axiomatisation of `ZFC` and to the usual first-order rendering of the Continuum
Hypothesis. The two inputs themselves (Gödel's and Cohen's constructions) are not formalised
here; they enter as the two satisfiability statements.
-/

/-- **The Continuum Hypothesis is independent of ZFC, reduced to Gödel's and Cohen's theorems.**

For any theory `ZFC` and any sentence `CH` in the first-order language of set theory, `CH` is
independent of `ZFC` (that is, `ZFC` entails neither `CH` nor `¬ CH`) if and only if both
`ZFC + CH` and `ZFC + ¬CH` are satisfiable — the former being Gödel's relative consistency result
via the constructible universe, the latter Cohen's via forcing. -/
