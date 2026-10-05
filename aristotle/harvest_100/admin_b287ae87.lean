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
def Level.rank : Level → Nat
  | .low => 0
  | .medium => 1
  | .high => 2

/-- Access mode of a request. -/
inductive Mode
  | read
  | write
  deriving DecidableEq, Repr, Inhabited

/-- Containment test on compartment sets, represented as lists of tags. -/
def subsetOf (a b : List Nat) : Bool := a.all (fun x => b.contains x)

/-- A protection domain: a security level together with a set of compartments. -/
structure Domain where
  level : Level
  compartments : List Nat
  deriving DecidableEq, Inhabited

/-- An access request of a subject domain on an object domain. -/
structure Request where
  subject : Domain
  object : Domain
  mode : Mode
  deriving DecidableEq, Inhabited

/-- The level check performed by the original isolation engine:
no read-up and no write-down. -/
def levelOk (r : Request) : Bool :=
  match r.mode with
  | .read => r.object.level.rank ≤ r.subject.level.rank
  | .write => r.subject.level.rank ≤ r.object.level.rank

/-- The additional compartment check used to tighten the engine. -/
def compartmentOk (r : Request) : Bool :=
  match r.mode with
  | .read => subsetOf r.object.compartments r.subject.compartments
  | .write => subsetOf r.subject.compartments r.object.compartments

/-- The original admission predicate of the isolation engine. -/
def original (r : Request) : Bool := levelOk r

/-- The tightened admission predicate: the original check conjoined with the
compartment guard. -/
def tightened (r : Request) : Bool := original r && compartmentOk r

/-- `p` refines `q` when every request admitted by `p` is admitted by `q`. -/
def Refines (p q : Request → Bool) : Prop := ∀ r : Request, p r = true → q r = true

/-! ## Soundness: the tightened predicate refines the original one -/

/-- **Main theorem.** The tightened admission predicate refines the original one:
every request admitted after tightening was already admitted before, so
tightening can only remove behaviours from the isolation engine. -/
theorem tightened_predicate_refines_original : Refines tightened original := by
  intro r hr
  have h : original r = true ∧ compartmentOk r = true := by
    simpa [tightened] using hr
  exact h.1

/-! ## Completeness: exactly the guard is lost -/

/-- Characterisation of the tightened predicate: it admits exactly those requests
that the original predicate admits and that additionally satisfy the compartment
guard. -/
theorem tightened_iff (r : Request) :
    tightened r = true ↔ original r = true ∧ compartmentOk r = true := by
  simp [tightened]

/-- If the compartment guard holds everywhere, tightening changes nothing. -/
theorem tightened_eq_original_of_guard (h : ∀ r : Request, compartmentOk r = true) :
    tightened = original := by
  funext r
  simp [tightened, h r]

/-- Refinement is reflexive. -/
theorem refines_refl (p : Request → Bool) : Refines p p := fun _ h => h

/-- Refinement is transitive. -/
theorem refines_trans {p q s : Request → Bool} (hpq : Refines p q) (hqs : Refines q s) :
    Refines p s := fun r h => hqs r (hpq r h)

/-- Refinement is antisymmetric, so mutual refinement is extensional equality. -/
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
def witness : Request :=
  { subject := { level := .high, compartments := [] }
    object := { level := .low, compartments := [0] }
    mode := .read }

/-- The refinement is strict: the tightened engine really rejects more requests. -/
theorem tightened_strictly_refines :
    original witness = true ∧ tightened witness = false := by
  constructor
  · decide
  · decide

/-- Consequently the tightened predicate is not equal to the original one. -/
theorem tightened_ne_original : tightened ≠ original := by
  intro h
  have h1 : tightened witness = original witness := congrFun h witness
  obtain ⟨ho, ht⟩ := tightened_strictly_refines
  rw [ht, ho] at h1
  exact Bool.noConfusion h1

/-- The original predicate does **not** refine the tightened one. -/
theorem not_refines_original_tightened : ¬ Refines original tightened := by
  intro h
  obtain ⟨ho, ht⟩ := tightened_strictly_refines
  have h1 := h witness ho
  rw [ht] at h1
  exact Bool.noConfusion h1

end PCA.Isolation

