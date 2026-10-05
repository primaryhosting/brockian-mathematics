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

theorem authorized_mono_roles (q : Request) (s : List Role)
    (hs : q.roles ⊆ s) (h : q.authorized) :
    ({ q with roles := s } : Request).authorized :=
  q.policy.mono hs h

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

