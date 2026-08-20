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

theorem bail_on_unrecognized_is_sound
    (E : Engine Req Act Cap) (hE : E.Certified) :
    (∀ r : Req, (∃ a : Act, E.recognize r = some a ∧ E.run r = Outcome.emit a)
        ∨ (E.recognize r = none ∧ E.run r = Outcome.bail))
      ∧ (∀ r : Req, (E.run r).Safe E)
      ∧ (∀ r : Req, E.recognize r = none → ∀ c : Cap, ¬ (E.run r).demand E c)
      ∧ (∀ r : Req, E.run r = Outcome.bail ↔ E.recognize r = none)
      ∧ (∀ (r : Req) (a : Act), E.run r = Outcome.emit a →
          CapSet.Subset (E.requires a) E.granted) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    cases h : E.recognize r with
    | none => exact Or.inr ⟨rfl, E.run_of_none h⟩
    | some a => exact Or.inl ⟨a, rfl, E.run_of_some h⟩
  · intro r
    cases h : E.recognize r with
    | none =>
        rw [E.run_of_none h]
        exact bail_is_safe E
    | some a =>
        rw [E.run_of_some h]
        exact hE r a h
  · intro r h c
    rw [E.run_of_none h]
    exact bail_demand_empty E c
  · intro r
    exact E.run_eq_bail_iff r
  · intro r a h
    exact hE r a ((E.run_eq_emit_iff r a).mp h)

end PCA.Coverage

#print axioms PCA.Coverage.bail_on_unrecognized_is_sound

