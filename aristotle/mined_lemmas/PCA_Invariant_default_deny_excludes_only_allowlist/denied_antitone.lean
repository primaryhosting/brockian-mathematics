/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Model of the isolation engine of a proof-carrying app.

A *request* is an attempt by a principal to perform an action on a resource.
An isolation engine is configured with a finite list of *grant rules*; each rule
recognises the set of requests that it authorises.  The engine is *default
deny*: it returns `allow` exactly when some configured rule authorises the
request, and returns `deny` in every other case.  The *allowlist* of an engine
is the collection of requests authorised by at least one of its rules.

The main invariant, `PCA.Invariant.default_deny_excludes_only_allowlist`, states
that the collection of requests excluded (denied) by the engine is *exactly* the
complement of the allowlist:

* soundness of isolation — every request outside the allowlist is denied; and
* completeness / no over-blocking — no request on the allowlist is denied.

This file is deliberately self-contained (it needs nothing beyond Lean's core
prelude); `RequestProject/Main.lean` re-packages the same statement using
Mathlib's `Set` API.
-/

namespace PCA

/-- A request: a principal attempting an action on a resource. -/
structure Request (P R A : Type _) where
  /-- The principal issuing the request. -/
  principal : P
  /-- The resource being accessed. -/
  resource : R
  /-- The action attempted on the resource. -/
  action : A

/-- The verdict returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A grant rule, given by the predicate describing the requests it authorises. -/
structure Rule (P R A : Type _) where
  /-- The requests authorised by this rule. -/
  admits : Request P R A → Prop

/-- An isolation engine is a finite configuration of grant rules. -/
structure Engine (P R A : Type _) where
  /-- The configured grant rules, in order. -/
  rules : List (Rule P R A)

variable {P R A : Type _}

/-- Collections of requests are modelled as predicates on requests. -/
abbrev ReqSet (P R A : Type _) := Request P R A → Prop

/-- The complement of a collection of requests. -/

theorem denied_antitone (eng eng' : Engine P R A)
    (hsub : ∀ r ∈ eng.rules, r ∈ eng'.rules) {req : Request P R A}
    (h : eng'.Denied req) : eng.Denied req := by
  refine denied_of_not_allowlist eng ?_
  rintro ⟨r, hr, hadm⟩
  have h' : ¬ eng'.Allowlist req :=
    (evaluate_eq_deny_iff_not_allowlist eng' req).1 h
  exact h' ⟨r, hsub r hr, hadm⟩

end Invariant

end PCA

import Mathlib
import RequestProject.DefaultDeny

/-!
# Default Deny Excludes Only Allowlist — Mathlib `Set` packaging

The target theorem `PCA.Invariant.default_deny_excludes_only_allowlist` lives in
`RequestProject/DefaultDeny.lean`, which is self-contained.  Here we restate it
using Mathlib's `Set` API: the set of requests denied by the default-deny
isolation engine is the set-theoretic complement of its allowlist.
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

set_option grind.warning false

namespace PCA

variable {P R A : Type*}

/-- The allowlist of an engine, as a Mathlib `Set`. -/
