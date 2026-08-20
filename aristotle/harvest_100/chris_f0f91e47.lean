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

namespace PCA

/-- A request presented to the isolation engine: a subject asking to perform an
action on a resource. -/
structure Request (S A R : Type*) where
  subject : S
  action : A
  resource : R
  deriving DecidableEq

/-- A capability grant held by the isolation engine's allowlist. -/
structure Grant (S A R : Type*) where
  subject : S
  action : A
  resource : R
  deriving DecidableEq

/-- The decision returned by the isolation engine. -/
inductive Decision
  | allow
  | deny
  deriving DecidableEq, Repr

variable {S A R : Type*}

/-- A grant matches a request when subject, action and resource all agree. -/
def Grant.Matches (g : Grant S A R) (r : Request S A R) : Prop :=
  g.subject = r.subject ∧ g.action = r.action ∧ g.resource = r.resource

instance [DecidableEq S] [DecidableEq A] [DecidableEq R]
    (g : Grant S A R) (r : Request S A R) : Decidable (g.Matches r) := by
  unfold Grant.Matches; infer_instance

/-- The allowlist induced by a list of capability grants: exactly those requests
covered by some grant. -/
def allowlist (caps : List (Grant S A R)) : Set (Request S A R) :=
  {r | ∃ g ∈ caps, g.Matches r}

/-- The isolation engine's evaluation function.  It is *default deny*: the answer
is `allow` only when some held capability matches, and `deny` in every other
case. -/
def eval [DecidableEq S] [DecidableEq A] [DecidableEq R]
    (caps : List (Grant S A R)) (r : Request S A R) : Decision :=
  if caps.any (fun g => decide (g.Matches r)) then Decision.allow else Decision.deny

section Engine

variable [DecidableEq S] [DecidableEq A] [DecidableEq R]

/-- Key intermediate lemma: the engine answers `allow` on exactly the requests of
the allowlist. -/
theorem eval_eq_allow_iff (caps : List (Grant S A R)) (r : Request S A R) :
    eval caps r = Decision.allow ↔ r ∈ allowlist caps := by
  unfold eval allowlist
  by_cases h : caps.any (fun g => decide (g.Matches r))
  · simp only [h, if_pos, Set.mem_setOf_eq, true_iff]
    simpa using h
  · simp only [h, Set.mem_setOf_eq, if_false, reduceCtorEq, false_iff]
    simpa using h

/-- The engine returns `deny` exactly when it does not return `allow`. -/
theorem eval_eq_deny_iff_ne_allow (caps : List (Grant S A R)) (r : Request S A R) :
    eval caps r = Decision.deny ↔ eval caps r ≠ Decision.allow := by
  unfold eval
  split <;> simp

namespace Invariant

/-- **Default deny excludes only the allowlist.**

The set of requests denied by the isolation engine is *exactly* the complement of
the allowlist: the engine is sound (it never denies a request covered by a held
capability) and complete (it denies every request not covered by one). -/
theorem default_deny_excludes_only_allowlist (caps : List (Grant S A R)) :
    {r : Request S A R | eval caps r = Decision.deny} = (allowlist caps)ᶜ := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  rw [eval_eq_deny_iff_ne_allow, ne_eq, eval_eq_allow_iff]

/-- Soundness: nothing on the allowlist is denied. -/
theorem allowlisted_not_denied (caps : List (Grant S A R)) (r : Request S A R)
    (hr : r ∈ allowlist caps) : eval caps r ≠ Decision.deny := by
  have := default_deny_excludes_only_allowlist (caps := caps)
  intro hd
  have : r ∈ (allowlist caps)ᶜ := this ▸ hd
  exact this hr

/-- Completeness: everything off the allowlist is denied. -/
theorem not_allowlisted_denied (caps : List (Grant S A R)) (r : Request S A R)
    (hr : r ∉ allowlist caps) : eval caps r = Decision.deny := by
  have h := default_deny_excludes_only_allowlist (caps := caps)
  have : r ∈ {r : Request S A R | eval caps r = Decision.deny} := by
    rw [h]; exact hr
  exact this

end Invariant

end Engine

end PCA

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

