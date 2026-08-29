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

def Pattern.Matches {α : Type _} : Pattern α → α → Prop
  | .any, _ => True
  | .exact v, w => v = w

instance {α : Type _} [DecidableEq α] (p : Pattern α) (v : α) :
    Decidable (Pattern.Matches p v) := by
  cases p with
  | any => exact isTrue trivial
  | exact w => exact (inferInstance : Decidable (w = v))

/-- A concrete capability request presented to the isolation engine: a subject
(the running app / principal), a resource, and an action. -/
structure Capability (S R A : Type _) where
  subject : S
  resource : R
  action : A
  deriving DecidableEq, Repr

/-- An allowlist rule: a pattern for each of the three components of a request. -/
structure Rule (S R A : Type _) where
  subject : Pattern S
  resource : Pattern R
  action : Pattern A
  deriving DecidableEq, Repr

/-- A rule *covers* a capability when all three of its patterns match. -/
