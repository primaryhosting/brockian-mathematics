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

theorem Cond.eval_eq_any_disjuncts {α : Type u} (σ : α → Bool) (c : Cond α) :
    c.eval σ = c.disjuncts.any (fun d => d.eval σ) := by
  induction c with
  | tt => simp [Cond.eval, Cond.disjuncts]
  | ff => simp [Cond.eval, Cond.disjuncts]
  | atom a => simp [Cond.eval, Cond.disjuncts]
  | not c _ => simp [Cond.eval, Cond.disjuncts]
  | and c₁ c₂ _ _ => simp [Cond.eval, Cond.disjuncts]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [Cond.eval, Cond.disjuncts, List.any_append, ih₁, ih₂]

/-- Decision semantics of a block of rules sharing one effect, prepended to a
remaining policy. -/
