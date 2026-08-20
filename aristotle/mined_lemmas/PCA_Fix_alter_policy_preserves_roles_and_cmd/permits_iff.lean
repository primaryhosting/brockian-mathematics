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
