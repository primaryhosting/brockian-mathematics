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
# A model of a proof-carrying-artifact (PCA) isolation engine

This file models a deterministic *isolation engine* together with the certificate
("proof-carrying artifact") mechanism used to attest a run of that engine, and proves
formal soundness and completeness of certificate re-checking:

  a recorded artifact re-proves (its certificate matches the one recomputed by replaying
  the program inside the engine) **iff** the artifact is untampered, i.e. it is exactly
  what an honest issuance of the engine on the declared program and initial state produces.
-/

namespace PCA

/-- Instructions of the isolated machine. `write` is the only externally visible effect. -/
inductive Instr where
  | push (n : ℤ)
  | add
  | write (ch : ℕ)
  | halt
  deriving DecidableEq

/-- A machine state: an operand stack, the (reversed) list of emitted outputs,
and the halted / faulted flags. -/
structure State where
  stack : List ℤ
  out : List (ℕ × ℤ)
  halted : Bool
  faulted : Bool
  deriving DecidableEq

/-- The isolation policy: the set of output channels the sandbox may write to. -/
structure Policy where
  allowed : ℕ → Bool

/-- Trapping: an attempted policy violation (or a malformed instruction) faults the
machine and stops it, rather than performing the effect. -/

noncomputable def issue (P : Policy) (prog : List Instr) (init : State) : Artifact :=
  { content := honestRecord P prog init, cert := digest (honestRecord P prog init) }

/-- The record the verifier recomputes by replaying the declared program inside the
engine (the *reproving* step). -/
