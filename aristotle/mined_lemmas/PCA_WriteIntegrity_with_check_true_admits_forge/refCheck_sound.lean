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

import Mathlib

/-!
# A formal model of the write-integrity isolation engine (`PCA`)

This file develops a small, self-contained operational model of an *isolation engine*
that mediates writes of principals (subjects) to resources (objects), and proves the
soundness / completeness statements for the reference monitor, together with the
"necessity" statement that a degenerate check (one that always returns `true`) admits
a forgery.

The integrity policy is the classical *no write up* rule: a subject may write an object
only if the subject's integrity level dominates the integrity level required by the object.

Main results:

* `PCA.WriteIntegrity.refCheck_sound` : the reference check only lets authorized writes through.
* `PCA.WriteIntegrity.refCheck_no_forge` : running the engine with the reference check never
  produces a forgery: any resource whose contents changed was written by an authorized write.
* `PCA.WriteIntegrity.refCheck_complete` : the reference check never blocks an authorized write;
  on authorized traces the mediated run agrees with the unmediated one.
* `PCA.WriteIntegrity.with_check_true_admits_forge` : the always-accepting check admits a forgery,
  so the check is load bearing.
-/

namespace PCA
namespace WriteIntegrity

/-- Principals (subjects) of the isolation engine. -/
abbrev Principal := ℕ

/-- Resources (objects) mediated by the isolation engine. -/
abbrev Resource := ℕ

/-- Values that can be stored in a resource. -/
abbrev Value := ℤ

/-- An environment assigns an integrity level to every principal and to every resource. -/
structure Env where
  /-- Integrity level of a principal. -/
  level : Principal → ℕ
  /-- Integrity level required in order to write a resource. -/
  required : Resource → ℕ

/-- A write request: principal `subj` asks to store `val` into resource `obj`. -/
structure Write where
  /-- The requesting principal. -/
  subj : Principal
  /-- The target resource. -/
  obj : Resource
  /-- The value to be written. -/
  val : Value

/-- The store: the current contents of every resource. -/

theorem refCheck_sound {E : Env} {w : Write} (h : refCheck E w = true) : Authorized E w := by
  simpa [refCheck] using h

/-- The reference check accepts every authorized write. -/
