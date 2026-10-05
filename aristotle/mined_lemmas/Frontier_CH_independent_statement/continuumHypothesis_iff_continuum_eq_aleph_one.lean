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

theorem continuumHypothesis_iff_continuum_eq_aleph_one :
    ContinuumHypothesis ↔ Cardinal.continuum.{0} = Cardinal.aleph 1 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le Cardinal.aleph_one_le_continuum.{0} with he | hl
    · exact he.symm
    · exact (h _ Cardinal.aleph0_lt_aleph_one hl).elim
  · intro h c h0 hc
    rw [h, ← Cardinal.succ_aleph0, Order.lt_succ_iff] at hc
    exact absurd h0 (not_lt.2 hc)

end Frontier

