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

theorem not_wf_of_alter_policy_changes {m : Manifest} (es : List Edit)
    (h : (alterPolicy m es).roles ≠ m.roles ∨ (alterPolicy m es).cmd ≠ m.cmd) :
    ¬ WF m := by
  intro hm
  rcases h with h | h
  · exact h (alter_policy_preserves_roles_and_cmd hm es).1
  · exact h (alter_policy_preserves_roles_and_cmd hm es).2

/-- Altering the policy is invisible to any observation that does not look at
the policy: the altered manifest agrees with the original on both remaining
fields simultaneously. -/
