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

theorem excludedSet_eq_compl_allowSet (p : Policy S R A) :
    p.excludedSet = (p.allowSet)ᶜ := by
  ext c
  simpa [Policy.excludedSet, Policy.allowSet, Set.mem_compl_iff] using
    deny_iff_not_mem_allowlist p c

/-- The allowlist and the excluded set cover everything. -/
