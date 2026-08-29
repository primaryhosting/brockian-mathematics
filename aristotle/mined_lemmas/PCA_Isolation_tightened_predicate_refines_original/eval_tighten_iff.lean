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

/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u

/-- Syntax of the isolation engine's access predicates over a state type `σ`.

An `AccessPred σ` describes when a request in state `s : σ` is permitted.
The language is monotone (no negation): `grant` always permits, `deny` never
permits, `atom p` consults a primitive check `p`, and `both`/`either` are
conjunction and disjunction of sub-policies. -/
inductive AccessPred (σ : Type u) : Type u
  | grant : AccessPred σ
  | deny : AccessPred σ
  | atom : (σ → Prop) → AccessPred σ
  | both : AccessPred σ → AccessPred σ → AccessPred σ
  | either : AccessPred σ → AccessPred σ → AccessPred σ

namespace AccessPred

/-- Denotational semantics of an access predicate: the set of states it permits. -/

theorem eval_tighten_iff {σ : Type u} (g p : AccessPred σ) (s : σ) :
    eval (tighten g p) s ↔ eval p s ∧ eval g s :=
  ⟨fun h => ⟨tightened_predicate_refines_original g p s h,
             tightened_predicate_enforces_guard g p s h⟩,
   fun h => tightened_predicate_complete g p s h.2 h.1⟩

/-- Refinement is transitive, so iterated tightening keeps refining the original. -/
