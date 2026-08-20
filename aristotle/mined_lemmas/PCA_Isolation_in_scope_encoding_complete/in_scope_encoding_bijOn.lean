/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The isolation model

An isolation engine mediates a guest application's requests against a *capability
scope*.  A scope grants access to everything underneath a root path, for a fixed
set of permitted operations.  Inside the sandbox the guest never sees absolute
paths: the engine hands it a *scope-relative encoding* of each request.

The target theorem `PCA.Isolation.in_scope_encoding_complete` states that, for
every scope, this encoding is a bijection between the in-scope requests and the
codes admissible for the scope:

* it maps in-scope requests to admissible codes (well-typedness of the model),
* it is injective on in-scope requests — *soundness*: two distinct in-scope
  requests are never confused inside the sandbox, and no information is lost,
* every admissible code is the encoding of some in-scope request — *completeness*:
  the encoding hides nothing that the scope actually grants, and conversely no
  admissible code refers to a resource outside the scope.

The only nontrivial ingredient is the path arithmetic, which is discharged by the
standard library lemma `List.prefix_iff_eq_append`
(`l₁ <+: l₂ ↔ l₁ ++ List.drop l₁.length l₂ = l₂`).

This file deliberately uses no imports beyond the automatic `Init`, so that the
required header comment can be the very first thing in the file; a Mathlib-phrased
restatement in terms of `Set.BijOn` is given in
`RequestProject/InScopeEncodingCompleteMathlib.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-- Operations an application may request on a resource. -/
inductive Op
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A capability scope: a root path together with the predicate describing the
permitted operations. -/
structure Scope where
  /-- Root of the region of the resource tree that the scope grants access to. -/
  root : List String
  /-- Operations permitted by the scope. -/
  ops : Op → Prop

/-- A request made by the guest application: an operation on an absolute path. -/
structure Request where
  /-- Absolute path of the requested resource. -/
  path : List String
  /-- Requested operation. -/
  op : Op

/-- A code, as seen by the guest: a scope-relative path together with an operation. -/
abbrev Code := List String × Op

/-- A request is *in scope* when its path lies under the scope root and its
operation is permitted by the scope. -/

theorem in_scope_encoding_bijOn (s : Scope) :
    Set.BijOn (encodeReq s) {r : Request | InScope s r} {c : Code | Admissible s c} := by
  obtain ⟨hmaps, hinj, hsurj⟩ := in_scope_encoding_complete s
  exact ⟨fun r hr => hmaps r hr, fun r₁ h₁ r₂ h₂ he => hinj r₁ r₂ h₁ h₂ he,
    fun c hc => hsurj c hc⟩

end PCA.Isolation

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

