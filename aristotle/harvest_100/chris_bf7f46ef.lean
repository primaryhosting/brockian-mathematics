import PCA.Coverage

/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The model

An *isolation engine* is the component of a proof-carrying app that decides whether
an incoming request falls inside the fragment of the input space the app has been
verified for (the *recognized* inputs), and, if so, produces a response.

The engine is modelled by

* a decidable recognizer `recognized : Input → Bool`, describing its coverage, and
* a handler `handle : Input → Output`, which is only trusted on recognized inputs.

The safety requirement of the app is an arbitrary specification
`spec : Input → Output → Prop`. The *coverage obligation* discharged when the app is
built is `CoverageCorrect`: the handler meets the spec on every recognized input.
Nothing whatsoever is known about the handler off the recognized fragment.

The engine's operational behaviour is *bail on unrecognized*: unrecognized inputs
produce the verdict `bail`, which emits no output at all.

The main theorem, `bail_on_unrecognized_is_sound`, says this policy is sound: every
output the engine ever emits satisfies the spec, even though the handler is
completely unconstrained outside its coverage. Completeness on the covered fragment
(`bail_on_unrecognized_is_complete`) and the fact that the guard is genuinely needed
(`unguarded_engine_can_be_unsound`) are also proved.
-/

namespace PCA.Coverage

universe u v

/-- The verdict returned by the isolation engine on a single input: either an
emitted output, or a refusal to act. -/
inductive Verdict (Output : Type v) : Type v
  | accept (o : Output) : Verdict Output
  | bail : Verdict Output
  deriving DecidableEq

/-- An isolation engine: a decidable recognizer describing the fragment of the input
space the app is verified for, together with a handler. -/
structure Engine (Input : Type u) (Output : Type v) where
  /-- The coverage test: which inputs the app claims to handle. -/
  recognized : Input → Bool
  /-- The response computed for an input. Only trusted on recognized inputs. -/
  handle : Input → Output

variable {Input : Type u} {Output : Type v}

/-- The bail-on-unrecognized operational semantics. -/
def Engine.run (E : Engine Input Output) (i : Input) : Verdict Output :=
  if E.recognized i then .accept (E.handle i) else .bail

/-- The unguarded semantics: always run the handler, whether or not the input is
recognized. -/
def Engine.runUnguarded (E : Engine Input Output) (i : Input) : Verdict Output :=
  .accept (E.handle i)

/-- The coverage obligation: the handler meets the specification on all recognized
inputs. This is what the app's proof establishes; it says nothing about
unrecognized inputs. -/
def CoverageCorrect (E : Engine Input Output) (spec : Input → Output → Prop) : Prop :=
  ∀ i, E.recognized i = true → spec i (E.handle i)

/-- Soundness of a semantics: every emitted output satisfies the specification. -/
def SoundFor (step : Input → Verdict Output) (spec : Input → Output → Prop) : Prop :=
  ∀ i o, step i = .accept o → spec i o

/-! ## Basic behaviour of the guarded engine -/

@[simp] theorem Engine.run_of_recognized (E : Engine Input Output) {i : Input}
    (h : E.recognized i = true) : E.run i = .accept (E.handle i) := by
  simp [Engine.run, h]

@[simp] theorem Engine.run_of_unrecognized (E : Engine Input Output) {i : Input}
    (h : E.recognized i = false) : E.run i = .bail := by
  simp [Engine.run, h]

/-- The engine emits an output exactly on the inputs it recognizes, and that output
is the handler's. -/
theorem Engine.run_eq_accept_iff (E : Engine Input Output) {i : Input} {o : Output} :
    E.run i = .accept o ↔ E.recognized i = true ∧ o = E.handle i := by
  unfold Engine.run
  cases h : E.recognized i <;> simp [eq_comm]

/-- The engine bails exactly on the inputs it does not recognize. -/
theorem Engine.run_eq_bail_iff (E : Engine Input Output) {i : Input} :
    E.run i = .bail ↔ E.recognized i = false := by
  unfold Engine.run
  cases h : E.recognized i <;> simp

/-! ## Main result -/

/-- **Bailing on unrecognized inputs is sound.**

If the handler of an isolation engine meets the specification on every input inside
its coverage, then the bail-on-unrecognized semantics is sound: any output it emits
satisfies the specification. No assumption at all is made about the handler outside
its coverage. -/
theorem bail_on_unrecognized_is_sound {Input : Type u} {Output : Type v}
    (E : Engine Input Output) (spec : Input → Output → Prop)
    (hcov : CoverageCorrect E spec) : SoundFor E.run spec := by
  intro i o hrun
  rw [Engine.run_eq_accept_iff] at hrun
  obtain ⟨hrec, rfl⟩ := hrun
  exact hcov i hrec

/-- **Completeness on the covered fragment.** On every recognized input the engine
does not bail, and the output it emits satisfies the specification. -/
theorem bail_on_unrecognized_is_complete (E : Engine Input Output)
    (spec : Input → Output → Prop) (hcov : CoverageCorrect E spec) {i : Input}
    (hrec : E.recognized i = true) : ∃ o, E.run i = .accept o ∧ spec i o :=
  ⟨E.handle i, E.run_of_recognized hrec, hcov i hrec⟩

/-- The guard is genuinely load-bearing: there is an engine whose coverage
obligation holds but whose unguarded semantics is unsound. -/
theorem unguarded_engine_can_be_unsound :
    ∃ (E : Engine Bool Bool) (spec : Bool → Bool → Prop),
      CoverageCorrect E spec ∧ SoundFor E.run spec ∧ ¬ SoundFor E.runUnguarded spec := by
  refine ⟨⟨fun i => i, fun _ => true⟩, fun i o => i = true ∧ o = true, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨hi, rfl⟩
  · exact bail_on_unrecognized_is_sound _ _ (fun i hi => ⟨hi, rfl⟩)
  · intro hsound
    have := hsound false true rfl
    simp at this

/-! ## Sequential runs

An app processes a stream of requests, bailing (and stopping) at the first request
outside its coverage. Soundness lifts to the whole trace: every output in an
accepted trace satisfies the specification for the corresponding input. -/

/-- Run the engine on a list of inputs, aborting at the first unrecognized one. -/
def Engine.runList (E : Engine Input Output) : List Input → Option (List Output)
  | [] => some []
  | i :: is => if E.recognized i then (E.runList is).map (E.handle i :: ·) else none

@[simp] theorem Engine.runList_nil (E : Engine Input Output) :
    E.runList [] = some [] := rfl

theorem Engine.runList_cons (E : Engine Input Output) (i : Input) (is : List Input) :
    E.runList (i :: is) =
      if E.recognized i then (E.runList is).map (E.handle i :: ·) else none := rfl

/-- A trace is accepted exactly when every input in it is recognized. -/
theorem Engine.runList_isSome_iff (E : Engine Input Output) (is : List Input) :
    (E.runList is).isSome ↔ ∀ i ∈ is, E.recognized i = true := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [Engine.runList_cons]
      cases h : E.recognized i with
      | false => simp [h]
      | true => simpa [h] using ih

/-- **Soundness of whole traces.** If the coverage obligation holds and the engine
accepts a trace of inputs, then the trace of emitted outputs has the same length as
the trace of inputs, and each emitted output satisfies the specification for the
input that produced it. -/
theorem runList_sound (E : Engine Input Output) (spec : Input → Output → Prop)
    (hcov : CoverageCorrect E spec) :
    ∀ (is : List Input) (os : List Output), E.runList is = some os →
      is.length = os.length ∧ ∀ p ∈ is.zip os, spec p.1 p.2 := by
  intro is
  induction is with
  | nil =>
      intro os h
      simp only [Engine.runList_nil, Option.some.injEq] at h
      subst h
      simp
  | cons i is ih =>
      intro os h
      rw [Engine.runList_cons] at h
      cases hrec : E.recognized i with
      | false => rw [hrec] at h; simp at h
      | true =>
          rw [hrec, if_pos rfl, Option.map_eq_some_iff] at h
          obtain ⟨os', hos', rfl⟩ := h
          obtain ⟨hlen, hall⟩ := ih os' hos'
          refine ⟨by simp [hlen], ?_⟩
          intro p hp
          rw [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hcov i hrec
          · exact hall p hp

end PCA.Coverage

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

