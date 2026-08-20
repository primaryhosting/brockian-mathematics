/-
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA

/-- The verdict returned by the isolation engine for a single request. -/
inductive Verdict
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A default-deny policy for requests of type `Req` is given by its allowlist:
the set of requests that are explicitly permitted. Everything else is denied. -/
structure Policy (Req : Type*) where
  /-- The set of explicitly permitted requests. -/
  allowlist : Set Req

variable {Req : Type*}

/-- The isolation engine's decision procedure: a request is allowed exactly when it
appears on the allowlist, and is denied otherwise (default deny). -/

theorem permitted_union_blocked (P : Policy Req) : P.permitted ∪ P.blocked = Set.univ := by
  rw [permitted_eq_allowlist, default_deny_excludes_only_allowlist]
  exact Set.union_compl_self _

/-- The empty allowlist blocks everything: pure default deny. -/
