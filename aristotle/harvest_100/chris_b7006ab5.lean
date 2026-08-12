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
def InScope (s : Scope) (r : Request) : Prop :=
  s.root <+: r.path ∧ s.ops r.op

/-- The scope-relative encoding presented to the guest application. -/
def encodeReq (s : Scope) (r : Request) : Code :=
  (r.path.drop s.root.length, r.op)

/-- Re-absolutising a code against the scope root. -/
def decodeReq (s : Scope) (c : Code) : Request :=
  ⟨s.root ++ c.1, c.2⟩

/-- The codes admissible for a scope: any relative path, with a permitted operation. -/
def Admissible (s : Scope) (c : Code) : Prop :=
  s.ops c.2

/-- Decoding undoes encoding on in-scope requests: the sandbox view loses no
information.  The path component is exactly `List.prefix_iff_eq_append`. -/
theorem decodeReq_encodeReq (s : Scope) {r : Request} (h : InScope s r) :
    decodeReq s (encodeReq s r) = r := by
  obtain ⟨hp, -⟩ := h
  cases r with
  | mk path op =>
    simp only [decodeReq, encodeReq, Request.mk.injEq, and_true]
    exact List.prefix_iff_eq_append.mp hp

/-- Encoding undoes decoding: every code is realised by its re-absolutisation. -/
theorem encodeReq_decodeReq (s : Scope) (c : Code) :
    encodeReq s (decodeReq s c) = c := by
  cases c with
  | mk rel op => simp [encodeReq, decodeReq]

/-- A decoded admissible code is always in scope: the engine never manufactures an
out-of-scope request from a code the guest is allowed to form. -/
theorem inScope_decodeReq (s : Scope) {c : Code} (hc : Admissible s c) :
    InScope s (decodeReq s c) :=
  ⟨⟨c.1, rfl⟩, hc⟩

/-- Encodings of in-scope requests are admissible codes. -/
theorem encodeReq_admissible (s : Scope) {r : Request} (h : InScope s r) :
    Admissible s (encodeReq s r) :=
  h.2

/-- The encoding is injective on in-scope requests. -/
theorem encodeReq_injOn (s : Scope) {r₁ r₂ : Request}
    (h₁ : InScope s r₁) (h₂ : InScope s r₂) (he : encodeReq s r₁ = encodeReq s r₂) :
    r₁ = r₂ := by
  have h := congrArg (decodeReq s) he
  rwa [decodeReq_encodeReq s h₁, decodeReq_encodeReq s h₂] at h

/-- **In-scope encoding completeness.**

For every capability scope, the scope-relative encoding is a bijection from the
in-scope requests onto the admissible codes: it is well defined into the
admissible codes, injective on in-scope requests (soundness), and surjective onto
the admissible codes (completeness). -/
theorem in_scope_encoding_complete (s : Scope) :
    (∀ r : Request, InScope s r → Admissible s (encodeReq s r)) ∧
    (∀ r₁ r₂ : Request, InScope s r₁ → InScope s r₂ →
      encodeReq s r₁ = encodeReq s r₂ → r₁ = r₂) ∧
    (∀ c : Code, Admissible s c → ∃ r : Request, InScope s r ∧ encodeReq s r = c) :=
  ⟨fun _ hr => encodeReq_admissible s hr,
   fun _ _ h₁ h₂ he => encodeReq_injOn s h₁ h₂ he,
   fun c hc => ⟨decodeReq s c, inScope_decodeReq s hc, encodeReq_decodeReq s c⟩⟩

end PCA.Isolation

import Mathlib
import RequestProject.InScopeEncodingComplete

/-!
# In-scope encoding completeness, Mathlib phrasing

`PCA.Isolation.in_scope_encoding_complete` (in
`RequestProject/InScopeEncodingComplete.lean`) says that the scope-relative
encoding is a bijection from the in-scope requests onto the admissible codes.
Here we repackage it as `Set.BijOn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-- The scope-relative encoding is a bijection from the set of in-scope requests
onto the set of admissible codes. -/
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

