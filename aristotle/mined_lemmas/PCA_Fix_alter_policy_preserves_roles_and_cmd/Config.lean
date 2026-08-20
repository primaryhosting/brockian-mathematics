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

def Config.authorizes (c : Config) (p : Principal) (r : Resource) (a : Action) : Bool :=
  permits c.policy c.roles p r a

/-- Soundness and completeness of the decision procedure with respect to its specification. -/
