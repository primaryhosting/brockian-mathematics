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
def CapSet (Cap : Type w) : Type w := Cap → Prop

/-- The empty capability set. -/
def CapSet.empty (Cap : Type w) : CapSet Cap := fun _ => False

/-- Pointwise inclusion of capability sets. -/
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
def Outcome.demand (E : Engine Req Act Cap) : Outcome Act → CapSet Cap
  | Outcome.emit a => E.requires a
  | Outcome.bail => CapSet.empty Cap

/-- An outcome is safe when everything it demands has been granted. -/
def Outcome.Safe (E : Engine Req Act Cap) (o : Outcome Act) : Prop :=
  CapSet.Subset (o.demand E) E.granted

/-- Running the engine: emit the recognized action, otherwise bail. -/
def Engine.run (E : Engine Req Act Cap) (r : Req) : Outcome Act :=
  match E.recognize r with
  | some a => Outcome.emit a
  | none => Outcome.bail

/-- The engine is *certified* when every action it can emit stays within the granted
capability budget. -/
def Engine.Certified (E : Engine Req Act Cap) : Prop :=
  ∀ (r : Req) (a : Act), E.recognize r = some a → CapSet.Subset (E.requires a) E.granted

/-!
## Basic characterisation of `run`
-/

theorem Engine.run_of_some {E : Engine Req Act Cap} {r : Req} {a : Act}
    (h : E.recognize r = some a) : E.run r = Outcome.emit a := by
  simp [Engine.run, h]

theorem Engine.run_of_none {E : Engine Req Act Cap} {r : Req}
    (h : E.recognize r = none) : E.run r = Outcome.bail := by
  simp [Engine.run, h]

/-- The engine bails exactly on the unrecognized requests. -/
theorem Engine.run_eq_bail_iff (E : Engine Req Act Cap) (r : Req) :
    E.run r = Outcome.bail ↔ E.recognize r = none := by
  cases hr : E.recognize r with
  | none => simp [Engine.run, hr]
  | some a => simp [Engine.run, hr]

/-- The engine emits `a` exactly when it recognizes the request as `a`. -/
theorem Engine.run_eq_emit_iff (E : Engine Req Act Cap) (r : Req) (a : Act) :
    E.run r = Outcome.emit a ↔ E.recognize r = some a := by
  cases hr : E.recognize r with
  | none => simp [Engine.run, hr]
  | some b => simp [Engine.run, hr]

/-- Bailing demands no capabilities whatsoever. -/
theorem bail_demand_empty (E : Engine Req Act Cap) (c : Cap) :
    ¬ (Outcome.bail : Outcome Act).demand E c := by
  intro h
  exact h

/-- Bailing is unconditionally safe, for any engine and any capability budget. -/
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

