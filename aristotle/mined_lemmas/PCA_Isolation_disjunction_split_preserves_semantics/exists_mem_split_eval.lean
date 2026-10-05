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

universe u v

namespace PCA
namespace Isolation

/-- Isolation policies: propositional guard expressions over atomic capability
checks of type `α`, as used by the isolation engine of a proof-carrying app. -/
inductive Policy (α : Type u) where
  | atom : α → Policy α
  | tru : Policy α
  | fls : Policy α
  | neg : Policy α → Policy α
  | and : Policy α → Policy α → Policy α
  | or : Policy α → Policy α → Policy α
  deriving DecidableEq, Repr

variable {α : Type u}

/-- Semantics of a policy relative to an environment assigning a truth value to
each atomic capability check. -/

theorem exists_mem_split_eval {env : α → Bool} {p : Policy α} (h : eval env p = true) :
    ∃ q ∈ split p, eval env q = true :=
  (disjunction_split_iff_exists env p).1 h

/-- The split is never empty. -/
