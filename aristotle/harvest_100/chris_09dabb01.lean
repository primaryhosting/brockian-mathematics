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
def fault (s : State) : State := { s with faulted := true, halted := true }

/-- One step of the isolation engine. -/
def step (P : Policy) (s : State) (i : Instr) : State :=
  if s.halted || s.faulted then s else
  match i with
  | .push n => { s with stack := n :: s.stack }
  | .add =>
      match s.stack with
      | a :: b :: rest => { s with stack := (a + b) :: rest }
      | _ => fault s
  | .write ch =>
      if P.allowed ch then
        match s.stack with
        | a :: rest => { s with stack := rest, out := (ch, a) :: s.out }
        | _ => fault s
      else fault s
  | .halt => { s with halted := true }

/-- Running a whole program: the final state. -/
def run (P : Policy) (s : State) (prog : List Instr) : State :=
  prog.foldl (step P) s

/-- The execution trace: the initial state followed by the state after each instruction. -/
def trace (P : Policy) (s : State) : List Instr → List State
  | [] => [s]
  | i :: is => s :: trace P (step P s i) is

/-! ## Basic properties of the engine -/

theorem run_nil (P : Policy) (s : State) : run P s [] = s := rfl

theorem run_cons (P : Policy) (s : State) (i : Instr) (prog : List Instr) :
    run P s (i :: prog) = run P (step P s i) prog := rfl

theorem trace_nil (P : Policy) (s : State) : trace P s [] = [s] := rfl

theorem trace_cons (P : Policy) (s : State) (i : Instr) (prog : List Instr) :
    trace P s (i :: prog) = s :: trace P (step P s i) prog := rfl

/-- The engine is deterministic: the trace is a function of the policy, the initial
state and the program (this is a definitional fact, recorded for readability). -/
theorem trace_deterministic (P : Policy) (s₁ s₂ : State) (p₁ p₂ : List Instr)
    (hs : s₁ = s₂) (hp : p₁ = p₂) : trace P s₁ p₁ = trace P s₂ p₂ := by
  subst hs; subst hp; rfl

/-- The trace is never empty. -/
theorem trace_ne_nil (P : Policy) (s : State) (prog : List Instr) : trace P s prog ≠ [] := by
  cases prog <;> simp [trace]

/-- The last state of the trace is the final state of the run. -/
theorem trace_getLast (P : Policy) (s : State) (prog : List Instr) :
    (trace P s prog).getLast? = some (run P s prog) := by
  induction prog generalizing s with
  | nil => rfl
  | cons i p ih =>
      rw [trace_cons, run_cons, List.getLast?_cons, ih]
      rfl

/-- **Isolation soundness**: the engine never emits on a channel the policy forbids. -/
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
def instrRepr : Instr → ℕ × ℤ
  | .push n => (0, n)
  | .add => (1, 0)
  | .write ch => (2, (ch : ℤ))
  | .halt => (3, 0)

theorem instrRepr_injective : Function.Injective instrRepr := by
  intro i j h
  cases i <;> cases j <;> simp [instrRepr, Prod.ext_iff] at h ⊢ <;> omega

/-- Injective encoding of states into plain data. -/
def stateRepr (s : State) : List ℤ × List (ℕ × ℤ) × Bool × Bool :=
  (s.stack, s.out, s.halted, s.faulted)

theorem stateRepr_injective : Function.Injective stateRepr := by
  intro s t h
  cases s; cases t
  simp only [stateRepr, Prod.mk.injEq] at h
  simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- Injective encoding of records into plain data. -/
def recordRepr (r : Record) :
    List (ℕ × ℤ) × (List ℤ × List (ℕ × ℤ) × Bool × Bool) ×
      List (List ℤ × List (ℕ × ℤ) × Bool × Bool) :=
  (r.prog.map instrRepr, stateRepr r.init, r.trace.map stateRepr)

theorem recordRepr_injective : Function.Injective recordRepr := by
  intro r₁ r₂ h
  cases r₁; cases r₂
  simp only [recordRepr, Prod.mk.injEq] at h
  obtain ⟨hp, hi, ht⟩ := h
  have hp' := (List.map_injective_iff.mpr instrRepr_injective) hp
  have ht' := (List.map_injective_iff.mpr stateRepr_injective) ht
  have hi' := stateRepr_injective hi
  simp [hp', hi', ht']

/-- The certificate digest: a collision-free (injective) encoding of the record. -/
noncomputable def digest (r : Record) : ℕ := Encodable.encode (recordRepr r)

theorem digest_injective : Function.Injective digest :=
  fun _ _ h => recordRepr_injective (Encodable.encode_injective h)

@[simp] theorem digest_eq_digest_iff (r₁ r₂ : Record) : digest r₁ = digest r₂ ↔ r₁ = r₂ :=
  ⟨fun h => digest_injective h, fun h => by rw [h]⟩

/-! ### Issuance, tampering, and re-proving -/

/-- The record an honest run of the engine produces for a program and initial state. -/
def honestRecord (P : Policy) (prog : List Instr) (init : State) : Record :=
  { prog := prog, init := init, trace := trace P init prog }

/-- The artifact an honest issuance of the engine produces. -/
noncomputable def issue (P : Policy) (prog : List Instr) (init : State) : Artifact :=
  { content := honestRecord P prog init, cert := digest (honestRecord P prog init) }

/-- The record the verifier recomputes by replaying the declared program inside the
engine (the *reproving* step). -/
def replay (P : Policy) (r : Record) : Record :=
  honestRecord P r.prog r.init

/-- An artifact is *untampered* when it is exactly what an honest issuance of the engine
on its own declared program and initial state produces. -/
def Untampered (P : Policy) (a : Artifact) : Prop :=
  a = issue P a.content.prog a.content.init

/-- The verifier's check: the stored certificate is the digest of the stored record, and
that digest agrees with the digest of the record obtained by replaying the program. -/
noncomputable def ReproveMatches (P : Policy) (a : Artifact) : Prop :=
  a.cert = digest a.content ∧ digest a.content = digest (replay P a.content)

/-- **Soundness and completeness of certificate re-checking.**
The recomputed certificate matches the stored one exactly when the artifact is
untampered. -/
theorem reprove_matches_iff_untampered (P : Policy) (a : Artifact) :
    ReproveMatches P a ↔ Untampered P a := by
  cases a with
  | mk r c =>
    simp only [ReproveMatches, Untampered, replay, issue, Artifact.mk.injEq]
    constructor
    · rintro ⟨hc, hd⟩
      have hr : r = honestRecord P r.prog r.init := digest_injective hd
      exact ⟨hr, by rw [hc, ← hr]⟩
    · rintro ⟨hr, hc⟩
      exact ⟨by rw [hc, ← hr], by rw [← hr]⟩


/-- Honest issuance always re-proves (the check is not vacuously false). -/
theorem reprove_matches_issue (P : Policy) (prog : List Instr) (init : State) :
    ReproveMatches P (issue P prog init) :=
  (reprove_matches_iff_untampered P _).mpr rfl

/-- Any artifact whose recorded trace is not the engine's own trace fails the check
(the check is not vacuously true). -/
theorem not_reprove_matches_of_trace_ne (P : Policy) (a : Artifact)
    (h : a.content.trace ≠ trace P a.content.init a.content.prog) : ¬ ReproveMatches P a := by
  intro hm
  have := (reprove_matches_iff_untampered P a).mp hm
  apply h
  conv_lhs => rw [this]
  rfl

/-- A concrete tampered artifact: the recorded trace is forged, so re-proving fails. -/
theorem exists_tampered_artifact_failing_reprove :
    ∃ (P : Policy) (a : Artifact), ¬ ReproveMatches P a := by
  refine ⟨⟨fun _ => true⟩, ⟨⟨[Instr.halt], ⟨[], [], false, false⟩, []⟩, 0⟩, ?_⟩
  apply not_reprove_matches_of_trace_ne
  simp [trace]

end Cert

end PCA

#print axioms PCA.Cert.reprove_matches_iff_untampered


