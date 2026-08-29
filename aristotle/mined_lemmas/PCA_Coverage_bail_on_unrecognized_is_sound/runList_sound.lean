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

