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

def memFormula {n : ℕ} (t₁ t₂ : setLanguage.Term (Empty ⊕ Fin n)) :
    setLanguage.BoundedFormula Empty n :=
  memSymbol.boundedFormula₂ t₁ t₂

/-! ### The target statement -/

/-- **Independence of the Continuum Hypothesis (semantic form).**

Let `ZFC` be any theory in the first-order language of set theory and let `CH` be any sentence
of that language.  Gödel's constructible-universe argument provides a model of `ZFC + CH`
(hypothesis `goedel`), and Cohen's forcing argument provides a model of `ZFC + ¬CH`
(hypothesis `cohen`).  From these two relative consistency results the independence of `CH`
over `ZFC` follows: `ZFC` entails neither `CH` nor `¬CH`, and hence — by the completeness
theorem — proves neither.  This is the Lean-checked reduction of the independence of the
Continuum Hypothesis to the two model constructions of Gödel and Cohen. -/
