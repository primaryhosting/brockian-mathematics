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

theorem bail_is_safe (E : Engine Req Act Cap) :
    (Outcome.bail : Outcome Act).Safe E := by
  intro c hc
  exact absurd hc (bail_demand_empty E c)

/-!
## Main theorem

`bail_on_unrecognized_is_sound` packages the soundness and completeness of the
bail-on-unrecognized discipline for a certified isolation engine:

1. **Totality / coverage.** Every request gets an outcome, and it is either the
   emission of the recognized action or a bail — nothing else can happen.
2. **Soundness.** *Every* outcome on *every* request is safe: the engine never
   demands a capability that was not granted.  In particular the unrecognized
   requests — the ones the handler table says nothing about — are handled safely.
3. **Zero demand on bail.** On an unrecognized request the engine demands no
   capability at all.
4. **Completeness of the bail rule.** The engine bails on a request if and only if
   that request is unrecognized: it never bails on recognized traffic, and never
   fabricates an action for unrecognized traffic.
5. **No unsafe emission.** Anything actually emitted is within budget.
-/

