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
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u

/-- Conditions of the isolation engine's policy language over an atom type `α`. -/
inductive Cond (α : Type u) : Type u
  | tt : Cond α
  | ff : Cond α
  | atom : α → Cond α
  | not : Cond α → Cond α
  | and : Cond α → Cond α → Cond α
  | or : Cond α → Cond α → Cond α

/-- Boolean semantics of a condition relative to a valuation `σ` of the atoms. -/

def permits {α : Type u} (σ : α → Bool) (p : Policy α) : Bool :=
  evalPolicy σ p == some Effect.allow

/-- Top-level disjunctive splitting of a condition: the list of its
top-level disjuncts. -/
