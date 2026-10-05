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

/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-! ## The capability model of the isolation engine -/

/-- A *pattern* used inside an allowlist rule: either the wildcard `any`, which
matches every value, or `exact v`, which matches only `v`. -/
inductive Pattern (α : Type _) where
  | any : Pattern α
  | exact : α → Pattern α
  deriving DecidableEq, Repr

/-- Does a pattern match a concrete value? -/

theorem deny_iff_not_mem_allowlist (p : Policy S R A) (c : Capability S R A) :
    p.evaluate c = Decision.deny ↔ ¬ p.Allowlist c := by
  constructor
  · intro h hmem
    rw [allow_complete p c hmem] at h
    exact Decision.noConfusion h
  · intro h
    rw [Policy.evaluate, if_neg (fun hb => h ((any_covers_iff p c).mp hb))]

/-- **Default deny excludes only the allowlist.**

The set of capability requests excluded (denied) by the isolation engine under
its default-deny policy is *exactly* the complement of the policy's allowlist:
nothing outside the allowlist is ever admitted (soundness) and nothing inside
the allowlist is ever excluded (completeness). -/
