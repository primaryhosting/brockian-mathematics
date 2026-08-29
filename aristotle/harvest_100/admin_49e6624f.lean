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
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Coverage

open scoped Classical

universe u v

variable {I : Type u} {O : Type v}

/-- An *isolation engine*: a recognizer predicate carving out the inputs the engine
claims to cover, together with a total handler producing a candidate output. -/
structure Engine (I : Type u) (O : Type v) where
  /-- The inputs the engine claims to recognize (its coverage domain). -/
  recognizes : I → Prop
  /-- The candidate output produced on a recognized input. -/
  handle : I → O

/-- The engine's observable behaviour: answer on recognized inputs, **bail** (return `none`)
on everything else. -/
noncomputable def Engine.run (E : Engine I O) (i : I) : Option O :=
  if E.recognizes i then some (E.handle i) else none

/-- Coverage obligation: on every recognized input the handler meets the specification.
This is the per-case proof that a proof-carrying app discharges. -/
def Engine.CoveredCorrect (E : Engine I O) (spec : I → O → Prop) : Prop :=
  ∀ i, E.recognizes i → spec i (E.handle i)

/-- Soundness of the engine: every *answer* it actually emits meets the specification.
Bailing out (`none`) is vacuously sound. -/
def Engine.Sound (E : Engine I O) (spec : I → O → Prop) : Prop :=
  ∀ i o, E.run i = some o → spec i o

@[simp]
theorem Engine.run_eq_none_iff (E : Engine I O) (i : I) :
    E.run i = none ↔ ¬ E.recognizes i := by
  unfold Engine.run
  by_cases h : E.recognizes i <;> simp [h]

/-- The `some`-case characterization; the injectivity step is core's `Option.some.injEq`. -/
@[simp]
theorem Engine.run_eq_some_iff (E : Engine I O) (i : I) (o : O) :
    E.run i = some o ↔ E.recognizes i ∧ E.handle i = o := by
  unfold Engine.run
  by_cases h : E.recognizes i <;> simp [h]

/-- On an unrecognized input the engine bails. -/
theorem Engine.bails_of_not_recognizes (E : Engine I O) {i : I} (h : ¬ E.recognizes i) :
    E.run i = none :=
  (E.run_eq_none_iff i).mpr h

/-- On a recognized input the engine does not bail; it answers with the handler's output. -/
theorem Engine.run_of_recognizes (E : Engine I O) {i : I} (h : E.recognizes i) :
    E.run i = some (E.handle i) :=
  (E.run_eq_some_iff i (E.handle i)).mpr ⟨h, rfl⟩

/-- **Bailing out on unrecognized inputs is sound.**

If the handler is correct on every input the engine recognizes, then the engine — which
answers on recognized inputs and abstains everywhere else — never emits an answer that
violates the specification. No assumption whatsoever is made about the handler's behaviour
outside the coverage domain. -/
theorem bail_on_unrecognized_is_sound (E : Engine I O) (spec : I → O → Prop)
    (hcov : E.CoveredCorrect spec) : E.Sound spec := by
  intro i o hrun
  rw [Engine.run_eq_some_iff] at hrun
  have hrec : E.recognizes i := hrun.1
  have hval : E.handle i = o := hrun.2
  exact hval ▸ hcov i hrec

/-- Conversely, soundness forces the coverage obligation: the statement above is exactly
the right one, not an artificially weak one. -/
theorem coveredCorrect_of_sound (E : Engine I O) (spec : I → O → Prop)
    (hs : E.Sound spec) : E.CoveredCorrect spec := fun i hrec =>
  hs i (E.handle i) (E.run_of_recognizes hrec)

/-- Soundness and the coverage obligation are equivalent. -/
theorem sound_iff_coveredCorrect (E : Engine I O) (spec : I → O → Prop) :
    E.Sound spec ↔ E.CoveredCorrect spec :=
  ⟨coveredCorrect_of_sound E spec, bail_on_unrecognized_is_sound E spec⟩

/-- Completeness relative to the coverage domain: the engine answers on exactly the inputs
it recognizes. -/
theorem Engine.isSome_run_iff (E : Engine I O) (i : I) :
    (E.run i).isSome ↔ E.recognizes i := by
  unfold Engine.run
  by_cases h : E.recognizes i <;> simp [h]

end PCA.Coverage

