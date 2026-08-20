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

def reproveDigest (E : Engine) (c : Config) (es : List Event) : Nat :=
  E.root (E.honestCert c es)

end Engine

namespace Cert

/-- The events a record claims were executed. -/
