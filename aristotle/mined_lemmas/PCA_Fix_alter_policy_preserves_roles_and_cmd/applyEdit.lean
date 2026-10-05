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

def applyEdit (p : Policy) : Edit → Policy
  | .setNet b => { p with allowNet := b }
  | .setFS b => { p with allowFS := b }
  | .setMem n => { p with memLimit := n }
  | .deny c => { p with denied := if c ∈ p.denied then p.denied else c :: p.denied }
  | .permit c => { p with denied := p.denied.filter (· ≠ c) }

/-- Effect of a list of edits, applied left to right. -/
