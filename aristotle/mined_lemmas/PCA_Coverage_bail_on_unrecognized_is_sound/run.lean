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
# A formal model of a "bail on unrecognized input" isolation engine

This file develops a small, self-contained formal model of the *isolation engine*
of a pattern-covering analyser (`PCA`), together with the soundness and
completeness statements of its `bail-on-unrecognized` policy.

## The model

* An `Engine` carries a finite (list) collection of recognized `patterns`, a
  matcher `applies : Pat → Req → Bool` telling which pattern applies to a
  request, and a `handler : Pat → Req → State → State` describing the effect of
  servicing a request through a given pattern.
* `dispatch` picks the first matching pattern, `Recognized r` says that some
  pattern in the engine's coverage applies `r`.
* `step` is the *fail-closed* one-step semantics: if a pattern applies, run its
  handler; otherwise **bail** (refuse to act) rather than guess.
* `run` iterates `step` over a trace of requests, stopping at the first bail.

## The guarantees

`PCA.Coverage.bail_on_unrecognized_is_sound` packages three facts, given only
that each individual handler preserves the isolation invariant `Inv` on the
requests it is allowed to service:

1. **Soundness (no escape).** Every state the engine can actually reach from an
   `Inv`-state satisfies `Inv`. No global coverage assumption is needed: the
   engine is safe on *arbitrary*, including adversarial, input.
2. **Completeness of the bail diagnosis (no spurious bails).** If the engine
   bails, this is witnessed by a genuinely unrecognized request in the trace.
3. **Liveness under coverage.** If every request in the trace is recognized,
   the engine never bails and terminates in a state satisfying `Inv`.
-/

namespace PCA
namespace Coverage

universe u v w

/-- The result of running the isolation engine: either a new state, or a
refusal to act (`bail`) because the input was not recognized. -/
inductive Outcome (State : Type u) where
  | ok : State → Outcome State
  | bail : Outcome State
  deriving Repr

/-- An isolation engine: a finite coverage of `patterns`, a matcher saying which
pattern applies to a request, and the state transformation performed when a
request is serviced through a pattern. -/
structure Engine (Pat : Type u) (Req : Type v) (State : Type w) where
  /-- The patterns the engine recognizes (its coverage). -/
  patterns : List Pat
  /-- `applies p r` says pattern `p` applies to request `r`. -/
  applies : Pat → Req → Bool
  /-- The state transformation performed when servicing `r` through `p`. -/
  handler : Pat → Req → State → State

namespace Engine

variable {Pat : Type u} {Req : Type v} {State : Type w}

/-- The pattern the engine selects for a request: the first one that applies. -/

def run (E : Engine Pat Req State) (s : State) : List Req → Outcome State
  | [] => Outcome.ok s
  | r :: rs =>
      match E.step s r with
      | Outcome.ok s' => E.run s' rs
      | Outcome.bail => Outcome.bail

/-- The obligation discharged for each individual pattern: its handler
preserves the isolation invariant on the requests it is allowed to service. -/
