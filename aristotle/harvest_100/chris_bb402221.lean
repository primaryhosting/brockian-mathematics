/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
/-!
## Overview

This file is a self-contained formalisation (it needs no imports beyond the Lean core
prelude, so that the module header above can literally begin the file) of:

* single-tape Turing machines over the binary alphabet, deterministic (`Frontier.DTM`) and
  nondeterministic (`Frontier.NTM`), with a *finite* state set `Fin (states + 1)`;
* their step semantics on a two-way infinite tape `Int → Sym`;
* time-bounded decision of a language, and the complexity classes `Frontier.P` and
  `Frontier.NP`;
* polynomial-time computable functions, Karp (polynomial-time many-one) reducibility
  `Frontier.PolyReducible`, NP-hardness and NP-completeness.

The target declaration `Frontier.P_vs_NP_statement` states the precise content of the
assertion `P ≠ NP`: the classes differ exactly when some language is decided by a
polynomial-time nondeterministic Turing machine but by no polynomial-time deterministic one.
The theorem is the conjunction of the (proved) inclusion `P ⊆ NP` with pure logic; the
assertion `P ≠ NP` itself is of course open, and is *not* proved here.
-/

namespace Frontier

/-! ## Words, languages, tapes -/

/-- The tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym : Type := Option Bool

/-- A word is a finite binary string. -/
abbrev Word : Type := List Bool

/-- A language is a set of binary words. -/
abbrev Language : Type := Word → Prop

/-- The initial tape holding the input word `x`: the `i`-th cell (for `i ≥ 0`) holds the
`i`-th bit of `x`, and all other cells are blank. -/
def initTape (x : Word) : Int → Sym := fun i => if 0 ≤ i then x[i.toNat]? else none

/-- `f` is bounded by a polynomial. -/
def IsPolyBounded (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n, f n ≤ c * n ^ k + c

/-- A machine instruction: move the head left, move it right, or write a symbol. -/
inductive Stmt : Type
  | left : Stmt
  | right : Stmt
  | write : Sym → Stmt
  deriving DecidableEq

/-- A configuration of a machine with `n` states: the current state, the tape contents and
the position of the head. -/
structure Cfg (n : Nat) : Type where
  /-- Current internal state. -/
  state : Fin n
  /-- Contents of the (two-way infinite) tape. -/
  tape : Int → Sym
  /-- Position of the head. -/
  pos : Int

/-- The configuration resulting from entering state `q'` and performing instruction `s`. -/
def applyStmt {n : Nat} (c : Cfg n) (q' : Fin n) : Stmt → Cfg n
  | .left => ⟨q', c.tape, c.pos - 1⟩
  | .right => ⟨q', c.tape, c.pos + 1⟩
  | .write a => ⟨q', fun i => if i = c.pos then a else c.tape i, c.pos⟩

/-- The starting configuration on input `x`: state `0`, head at position `0`, input written
on the tape. -/
def initCfg (n : Nat) (x : Word) : Cfg (n + 1) := ⟨0, initTape x, 0⟩

/-! ## Deterministic machines and the class `P` -/

/-- A deterministic single-tape Turing machine over the binary alphabet. Its state set is
`Fin (states + 1)`, with `0` the initial state; on state `q` reading symbol `a` it either
halts (`M q a = none`) or moves to a new state performing an instruction. -/
structure DTM : Type where
  /-- The machine has `states + 1` internal states. -/
  states : Nat
  /-- The transition function; `none` means "halt". -/
  M : Fin (states + 1) → Sym → Option (Fin (states + 1) × Stmt)
  /-- The accepting states. -/
  accept : Fin (states + 1) → Prop

/-- One step of a deterministic machine; `none` means the machine has halted. -/
def DTM.step (D : DTM) (c : Cfg (D.states + 1)) : Option (Cfg (D.states + 1)) :=
  (D.M c.state (c.tape c.pos)).map fun p => applyStmt c p.1 p.2

/-- `D.run t c` is the configuration reached from `c` after exactly `t` steps, and `none`
if the machine halted before then. -/
def DTM.run (D : DTM) : Nat → Cfg (D.states + 1) → Option (Cfg (D.states + 1))
  | 0, c => some c
  | t + 1, c => (D.run t c).bind D.step

/-- `D` decides `L` within time `f`: on every input `x` the machine halts after at most
`f |x|` steps, and the state it halts in is accepting exactly when `x ∈ L`. -/
def DTM.Decides (D : DTM) (L : Language) (f : Nat → Nat) : Prop :=
  ∀ x : Word, ∃ t ≤ f x.length, ∃ c : Cfg (D.states + 1),
    D.run t (initCfg D.states x) = some c ∧ D.step c = none ∧ (D.accept c.state ↔ L x)

/-- **The class `P`**: languages decided by a deterministic Turing machine within a
polynomial time bound. -/
def P : Language → Prop :=
  fun L => ∃ (D : DTM) (f : Nat → Nat), IsPolyBounded f ∧ D.Decides L f

/-! ## Nondeterministic machines and the class `NP` -/

/-- A nondeterministic single-tape Turing machine: in each state, reading each symbol, a
*set* of actions is available, an action being either halting (`none`) or a new state
together with an instruction. -/
structure NTM : Type where
  /-- The machine has `states + 1` internal states. -/
  states : Nat
  /-- The transition relation; the action `none` is the option of halting. -/
  M : Fin (states + 1) → Sym → Option (Fin (states + 1) × Stmt) → Prop
  /-- The accepting states. -/
  accept : Fin (states + 1) → Prop

/-- One nondeterministic step. -/
def NTM.Step (N : NTM) (c c' : Cfg (N.states + 1)) : Prop :=
  ∃ q' : Fin (N.states + 1), ∃ s : Stmt,
    N.M c.state (c.tape c.pos) (some (q', s)) ∧ c' = applyStmt c q' s

/-- A configuration in which the machine is allowed to halt. -/
def NTM.Halt (N : NTM) (c : Cfg (N.states + 1)) : Prop :=
  N.M c.state (c.tape c.pos) none

/-- `N.Reaches t c c'` means that `c'` is reachable from `c` by exactly `t` steps of some
computation branch. -/
def NTM.Reaches (N : NTM) : Nat → Cfg (N.states + 1) → Cfg (N.states + 1) → Prop
  | 0, c, c' => c = c'
  | t + 1, c, c' => ∃ c₁, N.Step c c₁ ∧ N.Reaches t c₁ c'

/-- `N` accepts `x` within `t` steps: some computation branch halts in an accepting state
after at most `t` steps. -/
def NTM.Accepts (N : NTM) (x : Word) (t : Nat) : Prop :=
  ∃ s ≤ t, ∃ c : Cfg (N.states + 1),
    N.Reaches s (initCfg N.states x) c ∧ N.Halt c ∧ N.accept c.state

/-- `N` decides `L` within time `f`: a word `x` belongs to `L` exactly when `N` accepts it
within `f |x|` steps. -/
def NTM.Decides (N : NTM) (L : Language) (f : Nat → Nat) : Prop :=
  ∀ x : Word, L x ↔ N.Accepts x (f x.length)

/-- **The class `NP`**: languages decided by a nondeterministic Turing machine within a
polynomial time bound. -/
def NP : Language → Prop :=
  fun L => ∃ (N : NTM) (f : Nat → Nat), IsPolyBounded f ∧ N.Decides L f

/-! ## Polynomial-time reducibility -/

/-- `D` outputs `y` on input `x` within `t` steps: it halts after at most `t` steps, with
the head back at position `0` and the encoding of `y` written on the tape. -/
def DTM.Outputs (D : DTM) (x y : Word) (t : Nat) : Prop :=
  ∃ s ≤ t, ∃ c : Cfg (D.states + 1), D.run s (initCfg D.states x) = some c ∧
    D.step c = none ∧ c.tape = initTape y ∧ c.pos = 0

/-- A function on words is polynomial-time computable when some deterministic machine
outputs its value within a polynomial number of steps. -/
def PolyTimeComputable (g : Word → Word) : Prop :=
  ∃ (D : DTM) (f : Nat → Nat), IsPolyBounded f ∧ ∀ x, D.Outputs x (g x) (f x.length)

/-- Karp reducibility: `L₁` reduces to `L₂` by a polynomial-time computable map. -/
def PolyReducible (L₁ L₂ : Language) : Prop :=
  ∃ g : Word → Word, PolyTimeComputable g ∧ ∀ x, L₁ x ↔ L₂ (g x)

/-- A language is NP-hard when every language in `NP` is polynomial-time reducible to it. -/
def NPHard (L : Language) : Prop := ∀ L', NP L' → PolyReducible L' L

/-- A language is NP-complete when it lies in `NP` and is NP-hard. -/
def NPComplete (L : Language) : Prop := NP L ∧ NPHard L

/-! ## Deterministic runs -/

theorem DTM.run_add (D : DTM) (a b : Nat) (c : Cfg (D.states + 1)) :
    D.run (a + b) c = (D.run a c).bind (fun c' => D.run b c') := by
  induction b with
  | zero => cases h : D.run a c <;> simp [DTM.run, h]
  | succ n ih =>
      have hab : a + (n + 1) = (a + n) + 1 := by omega
      rw [hab, DTM.run, ih]
      cases h : D.run a c with
      | none => simp [DTM.run]
      | some c₁ => simp [DTM.run]

theorem DTM.run_succ_left (D : DTM) (t : Nat) (c : Cfg (D.states + 1)) :
    D.run (t + 1) c = (D.step c).bind (fun c₁ => D.run t c₁) := by
  rw [show t + 1 = 1 + t by omega, DTM.run_add]
  simp [DTM.run]

theorem DTM.run_halted (D : DTM) {c : Cfg (D.states + 1)} (h : D.step c = none) (b : Nat) :
    D.run (b + 1) c = none := by
  induction b with
  | zero => exact h
  | succ n ih => show (D.run (n + 1) c).bind D.step = none; rw [ih]; rfl

/-- The halting configuration of a deterministic computation is unique. -/
theorem DTM.halt_unique (D : DTM) {c₀ c₁ c₂ : Cfg (D.states + 1)} {t₁ t₂ : Nat}
    (h₁ : D.run t₁ c₀ = some c₁) (hh₁ : D.step c₁ = none)
    (h₂ : D.run t₂ c₀ = some c₂) (hh₂ : D.step c₂ = none) : c₁ = c₂ := by
  cases Nat.le_total t₁ t₂ with
  | inl hle =>
      match Nat.le.dest hle with
      | ⟨b, hb⟩ =>
        rw [← hb, DTM.run_add, h₁] at h₂
        cases b with
        | zero =>
            have h3 : some c₁ = some c₂ := h₂
            exact Option.some.inj h3
        | succ n =>
            have h3 : D.run (n + 1) c₁ = some c₂ := h₂
            rw [D.run_halted hh₁] at h3
            cases h3
  | inr hle =>
      match Nat.le.dest hle with
      | ⟨b, hb⟩ =>
        rw [← hb, DTM.run_add, h₂] at h₁
        cases b with
        | zero =>
            have h3 : some c₂ = some c₁ := h₁
            exact (Option.some.inj h3).symm
        | succ n =>
            have h3 : D.run (n + 1) c₂ = some c₁ := h₁
            rw [D.run_halted hh₂] at h3
            cases h3

/-! ## Every deterministic machine is a nondeterministic machine -/

/-- A deterministic machine viewed as a nondeterministic machine, all of whose action sets
are singletons. -/
def DTM.toNTM (D : DTM) : NTM where
  states := D.states
  M := fun q a o => o = D.M q a
  accept := D.accept

@[simp] theorem DTM.toNTM_states (D : DTM) : D.toNTM.states = D.states := rfl

theorem DTM.toNTM_step {D : DTM} {c c' : Cfg (D.states + 1)} :
    D.toNTM.Step c c' ↔ D.step c = some c' := by
  constructor
  · intro hc
    match hc with
    | ⟨q', s, hs, hc'⟩ =>
      rw [hc']
      simp only [DTM.toNTM] at hs
      simp [DTM.step, ← hs]
  · intro h
    simp only [DTM.step, Option.map_eq_some_iff] at h
    match h with
    | ⟨⟨q', s⟩, hM, hc⟩ => exact ⟨q', s, by simp [DTM.toNTM, hM], hc.symm⟩

theorem DTM.toNTM_halt {D : DTM} {c : Cfg (D.states + 1)} :
    D.toNTM.Halt c ↔ D.step c = none := by
  cases h : D.M c.state (c.tape c.pos) with
  | none => simp [NTM.Halt, DTM.toNTM, DTM.step, h]
  | some p => simp [NTM.Halt, DTM.toNTM, DTM.step, h]

theorem DTM.toNTM_reaches {D : DTM} {t : Nat} {c c' : Cfg (D.states + 1)} :
    D.toNTM.Reaches t c c' ↔ D.run t c = some c' := by
  induction t generalizing c with
  | zero => simp [NTM.Reaches, DTM.run, eq_comm]
  | succ n ih =>
      rw [DTM.run_succ_left]
      constructor
      · intro hc
        match hc with
        | ⟨c₁, hstep, hrest⟩ =>
          rw [DTM.toNTM_step] at hstep
          rw [hstep]
          exact ih.1 hrest
      · intro h
        cases hstep : D.step c with
        | none =>
            rw [hstep] at h
            have h4 : (none : Option (Cfg (D.states + 1))) = some c' := h
            cases h4
        | some c₁ =>
            rw [hstep] at h
            exact ⟨c₁, DTM.toNTM_step.2 hstep, ih.2 h⟩

theorem DTM.toNTM_initCfg (D : DTM) (x : Word) :
    initCfg D.toNTM.states x = initCfg D.states x := rfl

/-- Every language in `P` is in `NP`. -/
theorem P_subset_NP : ∀ L : Language, P L → NP L := by
  intro L hL
  match hL with
  | ⟨D, f, hf, hdec⟩ =>
    refine ⟨D.toNTM, f, hf, ?_⟩
    intro x
    match hdec x with
    | ⟨t, ht, c, hrun, hhalt, hacc⟩ =>
      constructor
      · intro hx
        exact ⟨t, ht, c, DTM.toNTM_reaches.2 hrun, DTM.toNTM_halt.2 hhalt, hacc.2 hx⟩
      · intro hx
        match hx with
        | ⟨s, _, c', hreach, hhalt', hacc'⟩ =>
          have h1 : D.run s (initCfg D.states x) = some c' := DTM.toNTM_reaches.1 hreach
          have h2 : D.step c' = none := DTM.toNTM_halt.1 hhalt'
          have hc : c' = c := D.halt_unique h1 h2 hrun hhalt
          exact hacc.1 (hc ▸ hacc')

/-! ## Sanity checks: the classes are non-vacuous -/

/-- The machine with a single state that halts immediately; it accepts iff `b` holds. -/
def trivialDTM (b : Prop) : DTM where
  states := 0
  M := fun _ _ => none
  accept := fun _ => b

/-- Every constant language is decided in time `0`, hence lies in `P` (and so, by
`Frontier.P_subset_NP`, in `NP`). In particular `P` and `NP` are non-empty classes. -/
theorem constant_mem_P (b : Prop) : P (fun _ => b) :=
  ⟨trivialDTM b, fun _ => 0, ⟨0, 0, fun _ => Nat.zero_le _⟩, fun x =>
    ⟨0, Nat.le_refl 0, initCfg (trivialDTM b).states x, rfl, rfl, Iff.rfl⟩⟩

theorem constant_mem_NP (b : Prop) : NP (fun _ => b) :=
  P_subset_NP _ (constant_mem_P b)

/-! ## The statement -/

/-- **The P vs NP statement.** The complexity classes `P` and `NP` are different precisely
when there exists a language which is decided by some polynomial-time *nondeterministic*
Turing machine but by no polynomial-time *deterministic* Turing machine.

Whether this holds is the (open) P vs NP problem; the theorem below only makes the assertion
precise, by showing it equivalent to the existence of such a separating language. Its proof
combines pure logic with the inclusion `P ⊆ NP`, i.e. `Frontier.P_subset_NP`. -/
theorem P_vs_NP_statement : P ≠ NP ↔ ∃ L : Language, NP L ∧ ¬ P L := by
  constructor
  · intro h
    refine Classical.byContradiction (fun hc => h ?_)
    refine funext (fun L => propext ⟨P_subset_NP L, fun hL => ?_⟩)
    exact Classical.byContradiction (fun hPL => hc ⟨L, hL, hPL⟩)
  · intro hex h
    match hex with
    | ⟨L, hNP, hP⟩ => exact hP (h ▸ hNP)

/-- If some NP-complete language is not decidable in deterministic polynomial time, then
`P ≠ NP`. -/
theorem P_ne_NP_of_NPComplete_not_mem_P {L : Language} (hL : NPComplete L) (h : ¬ P L) :
    P ≠ NP :=
  P_vs_NP_statement.2 ⟨L, hL.1, h⟩

end Frontier


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

