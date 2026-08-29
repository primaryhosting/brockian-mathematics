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

theorem reqs_alterPolicy (f : Policy → Policy) (a : App) :
    reqs (alterPolicy f a) = reqs a := by
  induction a using App.rec_on_children with
  | leaf r => simp
  | node p cs ih =>
      simp only [alterPolicy_node, reqs_node, List.map_map]
      congr 1
      exact List.map_congr_left (fun c hc => by simpa using ih c hc)

end App

/-- **Main theorem.**  Rewriting the policies of an app preserves the roles and the commands of
all of its requests: the isolation engine's policy layer can change what an app is allowed to
do, but never what it asks to do. -/
