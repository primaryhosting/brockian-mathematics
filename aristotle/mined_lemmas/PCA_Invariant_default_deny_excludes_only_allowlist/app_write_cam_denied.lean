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

theorem app_write_cam_denied :
    samplePolicy.evaluate ⟨Subj.app, Res.cam, Act.write⟩ = Decision.deny := rfl

end Example

end PCA

import Mathlib
import RequestProject.PCA.Invariant

/-!
# Default deny, restated with Mathlib `Set`s

`RequestProject/PCA/Invariant.lean` must begin with the required header comment,
which in Lean 4 forces that module to have no `import` line.  This companion
module therefore re-exposes the main invariant in Mathlib's set-theoretic
language: the excluded (denied) requests form exactly the complement of the
policy's allowlist, and the two sets partition the space of requests.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

variable {S R A : Type _} [DecidableEq S] [DecidableEq R] [DecidableEq A]

/-- The allowlist of a policy, as a Mathlib `Set`. -/
