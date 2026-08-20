/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA

/-- Principals (subjects) of the isolation engine. -/
abbrev Principal := Nat

/-- Roles that principals may hold. -/
abbrev Role := Nat

/-- Resources that commands may touch. -/
abbrev Resource := Nat

/-- Actions a principal may attempt on a resource. -/
inductive Action
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A policy is a role-based grant table. -/
structure Policy where
  grants : Role → Resource → Action → Bool

/-- Commands of the sandboxed application. -/
inductive Cmd
  | nop
  | op (p : Principal) (r : Resource) (a : Action)
  | seq (c₁ c₂ : Cmd)
  deriving DecidableEq, Repr

/-- A configuration of the isolation engine: a role assignment, the residual command,
the currently installed policy, an audit epoch counter and an audit log. -/
structure Config where
  roles : Principal → List Role
  cmd : Cmd
  policy : Policy
  epoch : Nat
  log : List (Principal × Resource × Action)

/-- Installing a new policy: only the policy and the audit epoch counter change. -/
def Config.alterPolicy (c : Config) (p : Policy) : Config :=
  { c with policy := p, epoch := c.epoch + 1 }

/-- Installing a whole sequence of policies, in order. -/
def Config.alterAll (c : Config) : List Policy → Config
  | [] => c
  | p :: ps => (c.alterPolicy p).alterAll ps

/-- The engine's decision procedure: a principal may act if one of its roles is granted
the action on the resource by the installed policy. -/
def permits (pol : Policy) (roles : Principal → List Role)
    (p : Principal) (r : Resource) (a : Action) : Bool :=
  (roles p).any fun rl => pol.grants rl r a

/-- Declarative specification of authorization: there *exists* a held role carrying the grant. -/
inductive Permits (pol : Policy) (roles : Principal → List Role)
    (p : Principal) (r : Resource) (a : Action) : Prop
  | intro (rl : Role) (hmem : rl ∈ roles p) (hgrant : pol.grants rl r a = true) :
      Permits pol roles p r a

/-- Authorization decision taken in a configuration. -/
def Config.authorizes (c : Config) (p : Principal) (r : Resource) (a : Action) : Bool :=
  permits c.policy c.roles p r a

/-- Soundness and completeness of the decision procedure with respect to its specification. -/
theorem permits_iff (pol : Policy) (roles : Principal → List Role)
    (p : Principal) (r : Resource) (a : Action) :
    permits pol roles p r a = true ↔ Permits pol roles p r a := by
  constructor
  · intro h
    rw [permits, List.any_eq_true] at h
    obtain ⟨rl, hmem, hgrant⟩ := h
    exact ⟨rl, hmem, hgrant⟩
  · rintro ⟨rl, hmem, hgrant⟩
    rw [permits, List.any_eq_true]
    exact ⟨rl, hmem, hgrant⟩

/-- A single policy-alteration step of the engine. -/
inductive AlterStep : Config → Config → Prop
  | alter (c : Config) (p : Policy) : AlterStep c (c.alterPolicy p)

/-- Runs of the engine made of policy-alteration steps (reflexive-transitive closure). -/
inductive AlterRun : Config → Config → Prop
  | refl (c : Config) : AlterRun c c
  | tail {c d e : Config} (hrun : AlterRun c d) (hstep : AlterStep d e) : AlterRun c e

namespace Fix

/-- **Main theorem.**  Altering the installed policy of the isolation engine is
"frame preserving" for the security-relevant state that is *not* the policy:

1. a single `alterPolicy` leaves the role assignment and the residual command unchanged;
2. so does any finite sequence of policy alterations;
3. so does any run of the engine consisting of policy-alteration steps;
4. after an alteration, the engine's authorization decisions are exactly those of the
   new policy against the *unchanged* role assignment — i.e. altering the policy can
   neither smuggle in new roles nor rewrite the command;
5. and the decision procedure is sound and complete for the declarative specification
   of authorization after the alteration.
-/
theorem alter_policy_preserves_roles_and_cmd :
    (∀ (c : Config) (p : Policy),
        (c.alterPolicy p).roles = c.roles ∧ (c.alterPolicy p).cmd = c.cmd) ∧
    (∀ (c : Config) (ps : List Policy),
        (c.alterAll ps).roles = c.roles ∧ (c.alterAll ps).cmd = c.cmd) ∧
    (∀ (c c' : Config), AlterRun c c' → c'.roles = c.roles ∧ c'.cmd = c.cmd) ∧
    (∀ (c : Config) (p : Policy) (s : Principal) (r : Resource) (a : Action),
        (c.alterPolicy p).authorizes s r a = permits p c.roles s r a) ∧
    (∀ (c : Config) (p : Policy) (s : Principal) (r : Resource) (a : Action),
        ((c.alterPolicy p).authorizes s r a = true ↔ Permits p c.roles s r a)) := by
  refine ⟨fun c p => ⟨rfl, rfl⟩, ?_, ?_, fun c p s r a => rfl, ?_⟩
  · intro c ps
    induction ps generalizing c with
    | nil => exact ⟨rfl, rfl⟩
    | cons p ps ih =>
        obtain ⟨h₁, h₂⟩ := ih (c.alterPolicy p)
        exact ⟨h₁, h₂⟩
  · intro c c' h
    induction h with
    | refl => exact ⟨rfl, rfl⟩
    | tail hrun hstep ih =>
        obtain ⟨h₁, h₂⟩ := ih
        cases hstep with
        | alter q => exact ⟨h₁, h₂⟩
  · intro c p s r a
    exact permits_iff p c.roles s r a

end Fix

end PCA

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

