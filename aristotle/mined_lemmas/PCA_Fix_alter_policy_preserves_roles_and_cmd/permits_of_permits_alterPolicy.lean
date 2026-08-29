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
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Fix

/-! ## The isolation engine's model

An *app* is a tree of isolation scopes.  Each internal node carries a *policy*, which
restricts the ambient authority available to the subtree below it; each leaf carries a
*request*, consisting of the role under which the leaf runs and the command it wishes to
issue.  The isolation engine permits an app under an ambient policy exactly when every leaf
request is allowed by the ambient policy conjoined with all the policies guarding it. -/

/-- A role identifier. -/
abbrev Role := Nat

/-- A command identifier. -/
abbrev Cmd := Nat

/-- A request: a command issued under a given role. -/
structure Req where
  role : Role
  cmd : Cmd
  deriving DecidableEq

/-- A policy decides, for each role/command pair, whether the command is allowed. -/
abbrev Policy := Role → Cmd → Bool

/-- The always-permissive policy. -/

theorem permits_of_permits_alterPolicy {f : Policy → Policy}
    (hf : ∀ p, Policy.Le (f p) p) (amb : Policy) (a : App)
    (h : permits amb (alterPolicy f a) = true) : permits amb a = true := by
  induction a using App.rec_on_children generalizing amb with
  | leaf r => simpa using h
  | node p cs ih =>
      simp only [alterPolicy_node, permits_node, permitsAll_eq_true_iff, List.mem_map,
        forall_exists_index, and_imp] at h ⊢
      intro c hc
      refine ih c hc _ ?_
      refine permits_mono (amb := Policy.inter amb (f p)) ?_ _ (h _ c hc rfl)
      intro ro cm hro
      simp only [Policy.inter, Bool.and_eq_true] at hro ⊢
      exact ⟨hro.1, hf p ro cm hro.2⟩

/-- Altering the policies of an app leaves its requests untouched. -/
