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

theorem run_out_allowed (P : Policy) (s : State) (prog : List Instr)
    (h : ∀ q ∈ s.out, P.allowed q.1 = true) :
    ∀ q ∈ (run P s prog).out, P.allowed q.1 = true := by
  induction prog generalizing s with
  | nil => simpa [run_nil] using h
  | cons i p ih =>
      rw [run_cons]
      refine ih _ ?_
      intro q hq
      by_cases hhs : s.halted || s.faulted
      · simp only [step, hhs, if_pos] at hq
        exact h q hq
      · cases i with
        | push n => simp only [step, hhs, if_neg, Bool.false_eq_true, not_false_eq_true] at hq
                    exact h q hq
        | add =>
            simp only [step, hhs, Bool.false_eq_true, if_false] at hq
            match hst : s.stack with
            | [] => rw [hst] at hq; exact h q hq
            | [a] => rw [hst] at hq; exact h q hq
            | a :: b :: r => rw [hst] at hq; exact h q hq
        | write ch =>
            simp only [step, hhs, Bool.false_eq_true, if_false] at hq
            by_cases hc : P.allowed ch
            · rw [if_pos hc] at hq
              match hst : s.stack with
              | [] => rw [hst] at hq; exact h q hq
              | a :: r =>
                  rw [hst] at hq
                  simp only [List.mem_cons] at hq
                  rcases hq with hq | hq
                  · subst hq; simpa using hc
                  · exact h q hq
            · rw [if_neg hc] at hq; exact h q hq
        | halt => simp only [step, hhs, Bool.false_eq_true, if_false] at hq
                  exact h q hq

namespace Cert

/-- The content of an artifact that the certificate is computed over: the program,
the declared initial state, and the recorded trace. -/
structure Record where
  prog : List Instr
  init : State
  trace : List State
  deriving DecidableEq

/-- A proof-carrying artifact: a record together with its certificate. -/
structure Artifact where
  content : Record
  cert : ℕ

/-! ### A collision-free digest -/

/-- Injective encoding of instructions into a pair of numbers. -/
