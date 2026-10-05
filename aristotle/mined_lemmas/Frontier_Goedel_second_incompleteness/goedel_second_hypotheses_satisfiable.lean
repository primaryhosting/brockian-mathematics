/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## The syntactic setting

We work with the standard abstract (Hilbert–Bernays–Löb) formulation of Gödel's second
incompleteness theorem.

`Fml` is a language of sentences built from atoms, falsum and implication, together with a
unary operator `box`.  For a recursively axiomatized theory `T` extending `PA`, one reads
`Fml` as (a fragment of) the sentences of arithmetic and `box p` as the arithmetized
provability sentence `Prov_T(⌜p⌝)`; the fact that `T` is recursively axiomatized and extends
`PA` is exactly what supplies the three Löb derivability conditions `D1`, `D2`, `D3` recorded
in `ProvabilitySystem` below, and the diagonal lemma supplies the Gödel fixed point.
-/

/-- Sentences: propositional atoms, falsum, implication, and a provability operator `box`. -/
inductive Fml where
  | atom : Nat → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬ p := p → ⊥`. -/

theorem goedel_second_hypotheses_satisfiable :
    ∃ (T : ProvabilitySystem) (G : Fml), T.GoedelSentence G ∧ T.Consistent :=
  ⟨witnessSystem, Fml.bot, witnessSystem_goedelSentence, witnessSystem_consistent⟩

end Frontier

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

