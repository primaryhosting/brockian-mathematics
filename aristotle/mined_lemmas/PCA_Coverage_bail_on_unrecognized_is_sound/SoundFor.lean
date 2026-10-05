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

def SoundFor (step : Input → Verdict Output) (spec : Input → Output → Prop) : Prop :=
  ∀ i o, step i = .accept o → spec i o

/-! ## Basic behaviour of the guarded engine -/

