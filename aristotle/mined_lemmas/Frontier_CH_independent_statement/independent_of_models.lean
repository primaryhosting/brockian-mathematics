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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open FirstOrder FirstOrder.Language

universe u v

/-- A sentence `s0` is *independent* of a theory `T` when `T` neither entails `s0` nor entails
its negation.  By Gödel's completeness theorem (semantic entailment = derivability in
first-order logic) this is exactly the usual syntactic notion of independence. -/

theorem independent_of_models (h₁ : (T ∪ {s0}).IsSatisfiable)
    (h₂ : (T ∪ {s0.not}).IsSatisfiable) : Independent T s0 :=
  independent_iff_isSatisfiable.2 ⟨h₁, h₂⟩

/-- An independent sentence is in particular not entailed by the theory. -/
