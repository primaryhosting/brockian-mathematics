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
# A formal model of a policy-controlled isolation engine

This file develops a small but complete formal model of the *isolation engine* of a
privileged-command arbiter (`PCA`).  A request carries

* the set of `roles` held by the caller,
* the `cmd` (privileged command) that is being requested,
* the `policy` currently in force,

and the engine returns a boolean decision.  The engine is *deny-overrides*: a request is
executed when some held role is granted the command and no held role is denied it.

We prove:

* `PCA.Engine.decision_sound`  — the boolean engine only accepts requests that the
  declarative semantics `PCA.Permits` allows;
* `PCA.Engine.decision_complete` — the boolean engine accepts every request that the
  declarative semantics allows (so `PCA.Engine.decision_iff_permits` is an exact
  characterisation, i.e. the engine model is sound *and* complete);
* `PCA.Engine.isolation` — the decision only depends on the fragment of the policy that
  mentions the requested command: policies that agree on `cmd` are indistinguishable
  (command isolation / non-interference);
* the `PCA.Fix` layer: repairing a request by altering the policy, with
  `PCA.Fix.alter_policy_preserves_roles_and_cmd` as the key frame property, and
  `PCA.Fix.repair_permits` showing the repair really does make the request executable.
-/

namespace PCA

/-- A role identifier. -/
abbrev Role : Type := Nat

/-- A privileged command identifier. -/
abbrev Cmd : Type := Nat

/-- A policy is a pair of access-control lists: explicit grants and explicit denials,
each recorded as a `(role, command)` pair. -/
structure Policy where
  allow : List (Role × Cmd)
  deny : List (Role × Cmd)
  deriving DecidableEq, Repr

/-- A request presented to the isolation engine. -/
structure Request where
  roles : List Role
  cmd : Cmd
  policy : Policy
  deriving DecidableEq, Repr

namespace Policy

/-- `p.allows r c` holds when the policy explicitly grants command `c` to role `r`. -/

theorem decision_iff_permits (q : Request) :
    decision q = true ↔ Permits q.policy q.roles q.cmd :=
  ⟨decision_sound q, decision_complete q⟩

/-- **Command isolation** (non-interference): the decision on a request depends only on
the fragment of the policy that mentions the requested command.  Changing grants and
denials of *other* commands cannot change the decision. -/
