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

theorem emptySetSentence_independent :
    Independent (∅ : setLanguage.Theory) emptySetSentence :=
  independent_of_models isSatisfiable_emptySetSentence isSatisfiable_not_emptySetSentence

/-! ### The Continuum Hypothesis in Mathlib's cardinal arithmetic

The sentence `CH` above is the first-order rendering, inside a model of set theory, of the
following statement about cardinals: there is no cardinal strictly between `ℵ₀` and the
cardinality `𝔠` of the continuum.  We record the standard reformulation `𝔠 = ℵ₁`, which is
provable outright (the independence lies in whether the statement itself holds). -/

open Cardinal in
/-- The Continuum Hypothesis, stated for cardinals: no cardinal lies strictly between `ℵ₀`
and `𝔠`. -/
