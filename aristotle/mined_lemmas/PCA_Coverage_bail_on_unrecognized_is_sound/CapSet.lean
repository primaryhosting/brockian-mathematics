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

def CapSet.Subset {Cap : Type w} (s t : CapSet Cap) : Prop := ∀ c : Cap, s c → t c

/-- The outcome of running the isolation engine on a request: either an action is
emitted, or the engine bails out because the request was not recognized. -/
inductive Outcome (Act : Type u) : Type u
  | emit (a : Act) : Outcome Act
  | bail : Outcome Act

/-- An isolation engine: a partial recognizer, the capability demand of each action,
and the capabilities granted by the sandbox. -/
structure Engine (Req : Type u) (Act : Type v) (Cap : Type w) where
  /-- Classify a request; `none` means "unrecognized". -/
  recognize : Req → Option Act
  /-- The capabilities an action needs in order to execute. -/
  requires : Act → CapSet Cap
  /-- The capabilities the sandbox grants. -/
  granted : CapSet Cap

variable {Req : Type u} {Act : Type v} {Cap : Type w}

/-- The capabilities an outcome demands.  Bailing out demands nothing. -/
