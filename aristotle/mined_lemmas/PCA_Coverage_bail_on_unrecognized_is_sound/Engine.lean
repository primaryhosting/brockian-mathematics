/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Coverage

universe u v w

/-!
## The model

An *isolation engine* mediates between untrusted requests and a capability-guarded
runtime.  It carries a partial recognizer (a handler table), a capability demand for
each action it can emit, and the set of capabilities the ambient sandbox actually
grants.  The engine's totality discipline is *bail on unrecognized*: any request the
recognizer does not classify produces the inert `bail` outcome rather than a guess.

Capability sets are modelled as predicates `Cap → Prop`, with `Demands ⊆ Granted`
spelled out pointwise, so the development is self-contained.
-/

/-- A set of capabilities. -/

theorem Engine.run_eq_emit_iff (E : Engine Req Act Cap) (r : Req) (a : Act) :
    E.run r = Outcome.emit a ↔ E.recognize r = some a := by
  cases hr : E.recognize r with
  | none => simp [Engine.run, hr]
  | some b => simp [Engine.run, hr]

/-- Bailing demands no capabilities whatsoever. -/
