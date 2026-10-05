/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
# A formal model of a proof-carrying isolation engine and its audit certificates

This file develops a small but complete formal model of an *isolation engine*: a
deterministic machine that executes a sequence of events starting from a known
configuration, while emitting an audit **certificate** (`PCA.Cert`) that records the
starting configuration together with the whole transcript of
`(event, resulting configuration)` pairs.

A certificate is compressed to a single number, its **root digest**, by a hash chain built
from a compression function `mix` (the length of the transcript is folded in at the end,
so that transcripts of different lengths cannot be confused).

An auditor who does not trust a stored certificate can *reprove* it: re-execute the event
sequence inside the engine from the true starting configuration and recompute the root
digest (`PCA.Engine.reproveDigest`).  The main theorem
`PCA.Cert.reprove_matches_iff_untampered` states that this single-number comparison is
both **sound** and **complete**:

the recomputed digest equals the digest of the stored record **iff** the stored record is
untampered, i.e. it starts at the true initial configuration, reports exactly the events
that were really executed, and every recorded intermediate configuration is really the one
the engine's transition function produces.

The soundness direction is where the cryptographic hypotheses of the model (injectivity of
the serialisations and of the compression function) are used.
-/

namespace PCA

/-- An observable event consumed by the isolation engine. -/
structure Event where
  op : Nat
  arg : Nat
deriving DecidableEq

/-- A machine configuration of the isolation engine. -/
structure Config where
  regs : Nat
  mem : Nat
deriving DecidableEq

/-- An audit record produced by the isolation engine: the starting configuration together
with the transcript of `(event, resulting configuration)` pairs. -/
structure Cert where
  start : Config
  transcript : List (Event × Config)

/-- The model of an isolation engine:

* `step` is the deterministic transition function;
* `seed`, `encode` and `mix` are the serialisation / compression primitives used to build
  the root digest of a certificate;
* the three injectivity fields are the (idealised) collision-freedom assumptions on those
  primitives. -/
structure Engine where
  /-- Deterministic one-step transition of the isolated machine. -/
  step : Config → Event → Config
  /-- Serialisation of the initial configuration, used to seed the hash chain. -/
  seed : Config → Nat
  /-- Serialisation of one transcript entry. -/
  encode : Event → Config → Nat
  /-- Compression function of the hash chain. -/
  mix : Nat → Nat → Nat
  /-- The initial configuration can be recovered from its serialisation. -/
  seed_inj : Function.Injective seed
  /-- A transcript entry can be recovered from its serialisation. -/
  encode_inj : Function.Injective (fun p : Event × Config => encode p.1 p.2)
  /-- The compression function is collision-free. -/
  mix_inj : Function.Injective (fun p : Nat × Nat => mix p.1 p.2)

namespace Engine

/-- The transcript the engine really produces when it executes `es` from `c`. -/
def honestTranscript (E : Engine) (c : Config) : List Event → List (Event × Config)
  | [] => []
  | e :: es => (e, E.step c e) :: honestTranscript E (E.step c e) es

/-- The certificate the engine emits when it executes `es` from `c`. -/
def honestCert (E : Engine) (c : Config) (es : List Event) : Cert :=
  { start := c, transcript := E.honestTranscript c es }

/-- The hash chain: fold the compression function over a list of serialised entries. -/
def chain (E : Engine) (h : Nat) : List Nat → Nat
  | [] => h
  | x :: xs => chain E (E.mix h x) xs

/-- The root digest of a certificate: the hash chain over the serialised transcript,
seeded with the serialised starting configuration, with the transcript length folded in at
the end. -/
def root (E : Engine) (r : Cert) : Nat :=
  E.mix r.transcript.length
    (E.chain (E.seed r.start) (r.transcript.map (fun p => E.encode p.1 p.2)))

/-- Replaying a transcript from `c`: every recorded configuration is the one the engine's
transition function really produces. -/
def ReplayOK (E : Engine) (c : Config) : List (Event × Config) → Prop
  | [] => True
  | (e, c') :: t => E.step c e = c' ∧ ReplayOK E c' t

/-- *Reproving*: re-execute the events `es` from `c` inside the engine and recompute the
root digest of the resulting certificate. -/
def reproveDigest (E : Engine) (c : Config) (es : List Event) : Nat :=
  E.root (E.honestCert c es)

end Engine

namespace Cert

/-- The events a record claims were executed. -/
def events (r : Cert) : List Event := r.transcript.map Prod.fst

/-- A record is **untampered** with respect to the real execution of `es` from `c` when it
reports the true starting configuration, exactly the events that were really executed, and
only intermediate configurations that the engine's transition function really produces. -/
def Untampered (E : Engine) (r : Cert) (c : Config) (es : List Event) : Prop :=
  r.start = c ∧ r.events = es ∧ E.ReplayOK r.start r.transcript

end Cert

/-! ### Basic facts about honest transcripts -/

namespace Engine

@[simp] theorem honestTranscript_nil (E : Engine) (c : Config) :
    E.honestTranscript c [] = [] := rfl

@[simp] theorem honestTranscript_cons (E : Engine) (c : Config) (e : Event)
    (es : List Event) :
    E.honestTranscript c (e :: es) = (e, E.step c e) :: E.honestTranscript (E.step c e) es :=
  rfl

@[simp] theorem events_honestTranscript (E : Engine) :
    ∀ (c : Config) (es : List Event), (E.honestTranscript c es).map Prod.fst = es
  | _, [] => rfl
  | c, e :: es => by
      simp [honestTranscript_cons, events_honestTranscript E (E.step c e) es]

theorem replayOK_honestTranscript (E : Engine) :
    ∀ (c : Config) (es : List Event), E.ReplayOK c (E.honestTranscript c es)
  | _, [] => trivial
  | c, e :: es => ⟨rfl, replayOK_honestTranscript E (E.step c e) es⟩

/-- A transcript that replays correctly is the honest transcript of the events it
reports. -/
theorem eq_honestTranscript_of_replayOK (E : Engine) :
    ∀ (c : Config) (t : List (Event × Config)),
      E.ReplayOK c t → t = E.honestTranscript c (t.map Prod.fst)
  | _, [], _ => rfl
  | c, (e, c') :: t, h => by
      obtain ⟨hstep, htail⟩ := h
      subst hstep
      simpa using eq_honestTranscript_of_replayOK E (E.step c e) t htail

/-! ### Injectivity of the root digest -/

@[simp] theorem chain_nil (E : Engine) (h : Nat) : E.chain h [] = h := rfl

@[simp] theorem chain_cons (E : Engine) (h x : Nat) (xs : List Nat) :
    E.chain h (x :: xs) = E.chain (E.mix h x) xs := rfl

theorem mix_inj' (E : Engine) {a b c d : Nat} (h : E.mix a b = E.mix c d) : a = c ∧ b = d := by
  have := E.mix_inj (a₁ := (a, b)) (a₂ := (c, d)) h
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- The hash chain is collision-free on inputs of equal length. -/
theorem chain_inj (E : Engine) :
    ∀ (xs ys : List Nat) (h h' : Nat), xs.length = ys.length →
      E.chain h xs = E.chain h' ys → h = h' ∧ xs = ys
  | [], [], _, _, _, hc => ⟨hc, rfl⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | x :: xs, y :: ys, h, h', hl, hc => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [chain_cons] at hc
      obtain ⟨hmix, htail⟩ := chain_inj E xs ys (E.mix h x) (E.mix h' y) hl hc
      obtain ⟨hh, hxy⟩ := E.mix_inj' hmix
      exact ⟨hh, by rw [hxy, htail]⟩

/-- Distinct certificates have distinct root digests. -/
theorem root_inj (E : Engine) : Function.Injective E.root := by
  rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ h
  simp only [root] at h
  obtain ⟨hlen, hchain⟩ := E.mix_inj' h
  obtain ⟨hseed, hmap⟩ := E.chain_inj _ _ _ _ (by simpa using hlen) hchain
  have hs : s₁ = s₂ := E.seed_inj hseed
  have ht : t₁ = t₂ := List.map_injective_iff.2 E.encode_inj hmap
  rw [hs, ht]

end Engine

/-! ### Soundness and completeness of reproving -/

namespace Cert

/-- **Soundness and completeness of the isolation engine's audit model.**

Let the isolation engine `E` really execute the event sequence `es` starting from
configuration `c`, and let `r` be a stored audit record.  Recomputing the root digest by
re-running the engine (`E.reproveDigest c es`) matches the root digest of the stored record
**exactly when** the record is untampered, i.e. it reports the true starting
configuration, exactly the events that were really executed, and only intermediate
configurations that the engine's transition function really produces.

The forward implication is soundness (a matching digest cannot hide any tampering; this is
where the collision-freedom assumptions of the model are used), the backward implication
is completeness (an untampered record always reproduces the same digest). -/
theorem reprove_matches_iff_untampered (E : Engine) (c : Config) (es : List Event)
    (r : Cert) : E.root r = E.reproveDigest c es ↔ r.Untampered E c es := by
  constructor
  · intro h
    have hr : r = E.honestCert c es := E.root_inj h
    subst hr
    exact ⟨rfl, E.events_honestTranscript c es, E.replayOK_honestTranscript c es⟩
  · rintro ⟨hstart, hevents, hreplay⟩
    subst hstart
    have ht : r.transcript = E.honestTranscript r.start es := by
      have h := E.eq_honestTranscript_of_replayOK r.start r.transcript hreplay
      rwa [show r.transcript.map Prod.fst = es from hevents] at h
    have hr : r = E.honestCert r.start es := by
      cases r with
      | mk s t => simpa [Engine.honestCert] using ht
    rw [hr]
    rfl

end Cert

/-! ### The model is non-vacuous: a concrete isolation engine -/

namespace Engine

private theorem pair_uncurry_inj :
    Function.Injective (fun p : Nat × Nat => Nat.pair p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Nat.pair_eq_pair] at h
  simp [h.1, h.2]

/-- A concrete isolation engine: the machine adds the event's argument to its register and
writes the event's opcode into memory, and all serialisations are built from Cantor
pairing. -/
def sample : Engine where
  step c e := { regs := c.regs + e.arg, mem := e.op }
  seed c := Nat.pair c.regs c.mem
  encode e c := Nat.pair (Nat.pair e.op e.arg) (Nat.pair c.regs c.mem)
  mix := Nat.pair
  seed_inj := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Nat.pair_eq_pair] at h
    simp [h.1, h.2]
  encode_inj := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
    simp only [Nat.pair_eq_pair] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    simp [h1, h2, h3, h4]
  mix_inj := pair_uncurry_inj

instance : Nonempty Engine := ⟨sample⟩

end Engine

end PCA

