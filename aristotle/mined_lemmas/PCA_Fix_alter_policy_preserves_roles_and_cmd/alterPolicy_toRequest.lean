import Mathlib
import PCA.Fix

/-!
# Alter Policy Preserves Roles And Cmd — Mathlib (`Finset`) variant

Companion to `PCA.Fix`.  The target theorem
`PCA.Fix.alter_policy_preserves_roles_and_cmd` lives in `PCA/Fix.lean`, which
carries the required verbatim header comment and therefore cannot contain an
`import` line (a module docstring must follow, not precede, the imports).

Here the same isolation-engine model is redeveloped over Mathlib's `Finset`
role sets, and the corresponding preservation statement is proved, so that the
result is available in the Mathlib-flavoured setting as well.  A `Finset` model
is transported to the `List` model of `PCA.Fix` by
`PCA.Fix.FinsetModel.toRequest` (faithful when the list enumerates the role
set), and the two preservation theorems agree
(`PCA.Fix.FinsetModel.alterPolicy_toRequest`).
-/

set_option autoImplicit false

namespace PCA
namespace Fix
namespace FinsetModel

/-- A policy over `Finset` role sets: a role-monotone permission predicate. -/
structure Policy where
  /-- `permits roles c` holds when a principal owning `roles` may run `c`. -/
  permits : Finset Role → Cmd → Prop
  /-- Gaining roles never removes a permission. -/
  mono : ∀ {r s : Finset Role} {c : Cmd}, r ⊆ s → permits r c → permits s c

/-- A request whose caller roles form a `Finset`. -/
structure Request where
  /-- The roles held by the caller. -/
  roles : Finset Role
  /-- The command being requested. -/
  cmd : Cmd
  /-- The policy currently in force. -/
  policy : Policy

/-- The engine's verdict on a `Finset`-based request. -/

theorem alterPolicy_toRequest (q : Request) (p : Policy) (l : List Role) :
    toRequest (alterPolicy q p) l
      = PCA.Fix.alterPolicy (toRequest q l) p.toPolicy := rfl

end FinsetModel
end Fix
end PCA

/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace Fix

/-- A role name in the isolation engine's model. -/
abbrev Role := String

/-- A command name that an application may attempt to execute. -/
abbrev Cmd := String

/-- A policy of the isolation engine: it decides, for the roles held by the
caller and a command, whether that command is permitted. -/
structure Policy where
  /-- `permits roles c` holds when a principal owning `roles` may run `c`. -/
  permits : List Role → Cmd → Prop
  /-- Policies are monotone in the roles held: gaining roles never removes a
  permission. -/
  mono : ∀ {r s : List Role} {c : Cmd}, r ⊆ s → permits r c → permits s c

/-- A request submitted to the isolation engine: the roles held by the caller,
the command requested, and the policy in force. -/
structure Request where
  /-- The roles held by the caller. -/
  roles : List Role
  /-- The command being requested. -/
  cmd : Cmd
  /-- The policy currently in force. -/
  policy : Policy

/-- The engine authorizes a request exactly when the policy in force permits
the requested command for the caller's roles. -/
