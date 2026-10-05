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
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-! ## Model of the isolation engine

An *isolation engine* decides whether an access request from a subject domain to an
object domain is admissible.  The `original` admission predicate only compares
security *levels* (no read-up, no write-down).  The `tightened` predicate
additionally requires *compartment* containment.  The main result is that the
tightened predicate **refines** the original one: every request it admits was
already admitted by the original engine, so tightening can only remove
behaviours, never add them.

The model is fully decidable: all predicates are `Bool`-valued computations, so
concrete instances can be settled by `decide`. -/

/-- Security levels of the isolation engine. -/
inductive Level
  | low
  | medium
  | high
  deriving DecidableEq, Repr, Inhabited

/-- Numeric rank of a security level. -/

theorem refines_antisymm {p q : Request → Bool} (hpq : Refines p q) (hqp : Refines q p) :
    p = q := by
  funext r
  cases hp : p r <;> cases hq : q r
  · rfl
  · exact absurd (hqp r hq) (by simp [hp])
  · exact absurd (hpq r hp) (by simp [hq])
  · rfl

/-! ## Non-triviality: the refinement is strict -/

/-- A request that the original engine admits but the tightened engine rejects:
a `high` subject with no compartments reading a `low` object in compartment `0`. -/
