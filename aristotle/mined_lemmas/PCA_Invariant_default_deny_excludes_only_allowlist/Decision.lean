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

/-
Note on imports: a Lean module docstring must be the first command in the file and
`import` lines have to precede every command, so the header comment above rules out
any `import`.  The development below is therefore self-contained: it uses only the
Lean 4 core logic (`propext`, `funext`, `Classical`) and re-develops the handful of
set-theoretic notions (membership, complement, intersection, union, extensionality)
that the statement needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace PCA

/-! ## Sets of capabilities -/

/-- A set of capabilities, modelled as a predicate on the capability type. -/

theorem Decision.allow_ne_deny : Decision.allow ≠ Decision.deny := by
  intro h
  exact Decision.noConfusion h

/-- An isolation policy is given by its allowlist: the set of capabilities the
engine is explicitly permitted to grant.  Every other capability is denied by
default ("default deny"). -/
structure Policy (Cap : Type u) where
  /-- The set of explicitly permitted capabilities. -/
  allowlist : CapSet Cap

namespace Policy

variable {Cap : Type u}

open Classical in
/-- The default-deny evaluation function of the isolation engine: a capability is
allowed exactly when it appears on the allowlist, and denied otherwise. -/
