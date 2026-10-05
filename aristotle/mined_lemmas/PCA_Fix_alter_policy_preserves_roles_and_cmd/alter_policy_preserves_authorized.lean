/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` lines to precede every command, including module
-- doc comments, so this development is stated over Lean 4 core only (no imports)
-- in order to keep the mandated header comment at the very top of the file.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Fix

/-- A sandbox policy of the isolation engine: the syscalls the sandboxed
application may issue, whether it may touch the network, and its memory budget. -/
structure Policy where
  allowedSyscalls : List String
  netAccess : Bool
  maxMemMB : Nat
  deriving DecidableEq

/-- A proof-carrying application record: the command that is executed, the roles
granted to it by the deployment, and the isolation policy under which it runs. -/
structure App where
  cmd : String
  roles : List String
  policy : Policy
  deriving DecidableEq

/-- Rewrite the isolation policy of an application with the policy transformer `f`,
leaving every other component of the record untouched. -/

theorem alter_policy_preserves_authorized (a : App) (f : Policy → Policy) (r : String) :
    authorized (alterPolicy a f) r ↔ authorized a r := Iff.rfl

/-- Altering by the identity transformer is a no-op. -/
