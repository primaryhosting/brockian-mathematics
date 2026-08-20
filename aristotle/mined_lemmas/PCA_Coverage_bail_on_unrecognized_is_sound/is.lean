/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The model

An *isolation engine* processes a stream of events.  Each event is either
*recognized* (it lies inside the engine's verified coverage fragment) or not.
Recognized events are handled by the engine's `step` function; unrecognized
events cause the engine to *bail* into a designated safe fallback (`bail`).

The soundness statement we prove is the central design justification for this
architecture: to know that a safety invariant `Inv` holds along **every**
execution, it suffices to verify `step` on the **recognized** fragment only,
together with the (single, event-independent) fact that bailing is safe.

The development is self-contained: it needs nothing beyond Lean 4 core, so the
file has no imports.  (Mathlib's `List.foldl` API — e.g. `List.foldl_cons` —
would let one phrase `PCA.Coverage.Engine.run` as a `List.foldl`; the induction
below is the same one that `List.foldl` recursion performs, so no external

lemma is required.)
-/

namespace PCA
namespace Coverage

universe u v

/-- An isolation engine over a state space `S` and an event alphabet `E`.

* `recognized e` says that event `e` is inside the engine's verified
  coverage fragment;
* `step s e` is the handler used on recognized events;
* `bail s` is the safe fallback taken on unrecognized events. -/
structure Engine (S : Type u) (E : Type v) where
  /-- Coverage test: is this event inside the verified fragment? -/
  recognized : E → Bool
  /-- Handler for recognized events. -/
  step : S → E → S
  /-- Fallback taken on an unrecognized event. -/
  bail : S → S

variable {S : Type u} {E : Type v}

/-- One step of the engine: dispatch on recognition, bailing when the event is
outside the verified coverage fragment. -/
