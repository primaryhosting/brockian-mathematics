/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

/-- A principal of the isolation engine: either a root identity, or a principal
obtained by delegating from a parent principal under some capability name. -/
inductive Principal where
  | root : String → Principal
  | delegate : Principal → String → Principal
  deriving DecidableEq

namespace Principal

/-- `InChain q p` says that `q` occurs on the delegation chain of `p`, i.e. `q`
is `p` itself or one of its ancestors. -/

theorem denied_eq_compl_allowlist (A : Allowlist) (hA : DelegationClosed A) :
    (fun p => ¬ Permits A p) = fun p => ¬ A p := by
  funext p
  exact propext (default_deny_excludes_only_allowlist A hA p)

/-- Sanity check: the delegation-closure hypothesis is satisfiable by a
non-trivial allowlist, e.g. the one granting exactly the root principal `"app"`
and its direct delegation under the capability `"net"`. -/
example : DelegationClosed
    (fun p => p = Principal.root "app" ∨
      p = Principal.delegate (Principal.root "app") "net") := by
  intro p n h
  cases h with
  | inl h => exact Principal.noConfusion h
  | inr h =>
      injection h with h1 _
      exact Or.inl h1

end Invariant
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

