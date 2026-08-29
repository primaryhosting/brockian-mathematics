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

/-- Guards of the isolation engine's policy language: boolean combinations of
atomic predicates over an environment. -/
inductive Guard (α : Type u) : Type _
  | atom : α → Guard α
  | tru : Guard α
  | fls : Guard α
  | neg : Guard α → Guard α
  | conj : Guard α → Guard α → Guard α
  | disj : Guard α → Guard α → Guard α

/-- Semantics of a guard relative to an environment assigning truth values to atoms. -/

theorem any_splitGuard_eval {α : Type u} (env : α → Bool) (g : Guard α) :
    ((splitGuard g).any (fun h => h.eval env)) = g.eval env := by
  induction g with
  | disj g₁ g₂ ih₁ ih₂ =>
      simp [splitGuard, Guard.eval, List.any_append, ih₁, ih₂]
  | _ => simp [splitGuard]

/-- Split a single rule into the rules obtained from its top-level disjuncts,
keeping the same action. -/
