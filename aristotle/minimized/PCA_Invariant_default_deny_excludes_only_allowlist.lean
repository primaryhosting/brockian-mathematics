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

noncomputable def Policy.eval (P : Policy Req) (r : Req) : Verdict :=
  if r ∈ P.allowlist then Verdict.allow else Verdict.deny

/-- The set of requests the engine permits. -/

def Policy.permitted (P : Policy Req) : Set Req := {r | P.eval r = Verdict.allow}

/-- The set of requests the engine blocks. -/

def Policy.blocked (P : Policy Req) : Set Req := {r | P.eval r = Verdict.deny}

@[simp]

theorem Policy.eval_eq_allow_iff (P : Policy Req) (r : Req) :
    P.eval r = Verdict.allow ↔ r ∈ P.allowlist := by
  unfold Policy.eval
  split <;> simp_all

@[simp]

theorem Policy.eval_eq_deny_iff (P : Policy Req) (r : Req) :
    P.eval r = Verdict.deny ↔ r ∉ P.allowlist := by
  unfold Policy.eval
  split <;> simp_all

namespace Invariant

/-- **Soundness of default deny**: everything the engine permits is on the allowlist. -/

theorem permitted_subset_allowlist (P : Policy Req) : P.permitted ⊆ P.allowlist := by
  intro r hr
  simpa [Policy.permitted] using hr

/-- **Completeness of default deny**: everything on the allowlist is permitted. -/
