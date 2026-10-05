/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace PCA.Fix

/-! ## The isolation engine model

A *proof-carrying app* is described by a manifest consisting of

* a command line (`cmd`),
* a list of granted roles (`roles`),
* an isolation policy (`policy`).

The isolation engine only ever produces *canonical* manifests: empty command
arguments are dropped and the role list is canonicalised (deduplicated and put
into a fixed order of decreasing privilege).  Re-configuring an app by applying
a list of policy edits re-runs the engine's build pipeline, so a priori it could
also change the command line or the roles.  The target theorem states that on
well-formed (i.e. engine-produced) manifests this never happens: altering the
policy preserves roles and command exactly. -/

/-- The roles an app can be granted. -/
inductive Role
  | reader
  | writer
  | admin
  deriving DecidableEq, Repr

/-- All roles, in the engine's canonical order (decreasing privilege). -/

def allRoles : List Role := [Role.admin, Role.writer, Role.reader]

/-- An isolation policy. -/
structure Policy where
  allowNet : Bool
  allowFS : Bool
  memLimit : Nat
  denied : List String
  deriving DecidableEq, Repr

/-- A single policy edit. -/
inductive Edit
  | setNet (b : Bool)
  | setFS (b : Bool)
  | setMem (n : Nat)
  | deny (cap : String)
  | permit (cap : String)
  deriving Repr

/-- Effect of a single edit on a policy. -/
