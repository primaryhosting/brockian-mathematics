/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file gives a self-contained formalization of the complexity classes `P` and `NP` in
terms of time-bounded (deterministic and nondeterministic) single-tape Turing machines
over the binary alphabet, together with polynomial-time many-one reducibility `≤p`.

Mathlib provides Turing machine models (`Turing.TM0`, `Turing.TM1`, `Turing.TM2`, …) but
no notion of *time-bounded* computation and no complexity classes, so the model below is
developed from scratch; no Mathlib lemma comes close to settling `P = NP`, which is of
course open.  (The file uses only Lean core, so that the required header comment can be
the very first thing in it.)

The open problem itself is recorded as the proposition `Frontier.PNeqNP := P ≠ NP`, and
the theorem `Frontier.P_vs_NP_statement` proves the standard reformulation

  `P ≠ NP ↔ ∃ L, NP L ∧ ¬ P L`,

which is exactly the content of the statement "P ≠ NP" once one knows `P ⊆ NP`
(`Frontier.P_subset_NP`, also proved here).
-/

namespace Frontier

/-- Tape symbols: `none` is the blank symbol, `some b` a bit. -/
abbrev Sym := Option Bool

/-- A language is a set of finite bit strings. -/
abbrev Language := List Bool → Prop

/-- Head movements. -/
inductive Move where
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- Apply a head movement to a head position. -/
def Move.apply : Move → Int → Int
  | Move.left, i => i - 1
  | Move.right, i => i + 1
  | Move.stay, i => i

/-- Overwrite the symbol in cell `j` of a tape. -/
def writeTape (t : Int → Sym) (j : Int) (s : Sym) : Int → Sym :=
  fun i => if i = j then s else t i

/-- A configuration of a machine with `n` states: current state, head position and tape
contents (a bi-infinite tape indexed by `Int`). -/
structure Cfg (n : Nat) where
  state : Fin n
  head : Int
  tape : Int → Sym

/-- A deterministic single-tape Turing machine with `size` states, distinguished start
state `start`, a set `accept` of accepting states, and a partial transition function
`next` (the value `none` means "halt"). -/
structure Machine where
  size : Nat
  start : Fin size
  accept : Fin size → Bool
  next : Fin size → Sym → Option (Fin size × Sym × Move)

/-- A nondeterministic single-tape Turing machine: the transition function returns the
(finite) list of possible successors. -/
structure NMachine where
  size : Nat
  start : Fin size
  accept : Fin size → Bool
  next : Fin size → Sym → List (Fin size × Sym × Move)

/-- The tape holding the input string `x` in cells `0, 1, …, |x| - 1`, blank elsewhere. -/
def inputTape (x : List Bool) : Int → Sym :=
  fun i => if 0 ≤ i then x[i.toNat]? else none

/-- The initial configuration of a deterministic machine on input `x`. -/
def Machine.init (M : Machine) (x : List Bool) : Cfg M.size :=
  { state := M.start, head := 0, tape := inputTape x }

/-- The initial configuration of a nondeterministic machine on input `x`. -/
def NMachine.init (M : NMachine) (x : List Bool) : Cfg M.size :=
  { state := M.start, head := 0, tape := inputTape x }

/-- One step of a deterministic machine (`none` if the machine has halted). -/
def Machine.step (M : Machine) (c : Cfg M.size) : Option (Cfg M.size) :=
  (M.next c.state (c.tape c.head)).map fun p =>
    { state := p.1, head := p.2.2.apply c.head, tape := writeTape c.tape c.head p.2.1 }

/-- The possible successors of a configuration of a nondeterministic machine. -/
def NMachine.step (M : NMachine) (c : Cfg M.size) : List (Cfg M.size) :=
  (M.next c.state (c.tape c.head)).map fun p =>
    { state := p.1, head := p.2.2.apply c.head, tape := writeTape c.tape c.head p.2.1 }

/-- Running a deterministic machine for `n` steps. -/
def Machine.run (M : Machine) : Cfg M.size → Nat → Option (Cfg M.size)
  | c, 0 => some c
  | c, (n + 1) => (M.step c).bind fun c' => M.run c' n

/-- `M.reaches c n c'` : the nondeterministic machine `M` can go from `c` to `c'` in
exactly `n` steps. -/
def NMachine.reaches (M : NMachine) : Cfg M.size → Nat → Cfg M.size → Prop
  | c, 0, c' => c = c'
  | c, (n + 1), c' => ∃ d, d ∈ M.step c ∧ M.reaches d n c'

/-- A time bound is polynomial if it is dominated by `c * n ^ k + c`. -/
def IsPoly (T : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n, T n ≤ c * n ^ k + c

/-- The deterministic machine `M` decides the language `L` within time `T`: on every input
`x` it halts after at most `T |x|` steps, in an accepting state exactly when `x ∈ L`. -/
def Machine.DecidesIn (M : Machine) (L : Language) (T : Nat → Nat) : Prop :=
  ∀ x : List Bool, ∃ n, n ≤ T x.length ∧ ∃ c : Cfg M.size,
    M.run (M.init x) n = some c ∧ M.step c = none ∧ (M.accept c.state = true ↔ L x)

/-- The nondeterministic machine `M` accepts `x` within `t` steps: some computation path
of length at most `t` ends in an accepting halting configuration. -/
def NMachine.AcceptsIn (M : NMachine) (x : List Bool) (t : Nat) : Prop :=
  ∃ n, n ≤ t ∧ ∃ c : Cfg M.size,
    M.reaches (M.init x) n c ∧ M.step c = [] ∧ M.accept c.state = true

/-- The class **P**: languages decided by a deterministic Turing machine in polynomial
time. -/
def P (L : Language) : Prop :=
  ∃ (M : Machine) (T : Nat → Nat), IsPoly T ∧ M.DecidesIn L T

/-- The class **NP**: languages accepted by a nondeterministic Turing machine in
polynomial time. -/
def NP (L : Language) : Prop :=
  ∃ (M : NMachine) (T : Nat → Nat), IsPoly T ∧ ∀ x, L x ↔ M.AcceptsIn x (T x.length)

/-- `TapeOutput t y` says that the tape `t` contains exactly the string `y` in the cells
`0, 1, …, |y| - 1` and is blank in all other nonnegative cells. -/
def TapeOutput (t : Int → Sym) (y : List Bool) : Prop :=
  ∀ i : Int, 0 ≤ i → t i = y[i.toNat]?

/-- The deterministic machine `M` computes the string function `f` within time `T`. -/
def Machine.ComputesIn (M : Machine) (f : List Bool → List Bool) (T : Nat → Nat) : Prop :=
  ∀ x : List Bool, ∃ n, n ≤ T x.length ∧ ∃ c : Cfg M.size,
    M.run (M.init x) n = some c ∧ M.step c = none ∧ TapeOutput c.tape (f x)

/-- A string function is polynomial-time computable. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : Machine) (T : Nat → Nat), IsPoly T ∧ M.ComputesIn f T

/-- Polynomial-time many-one reducibility: `L ≤p K` iff there is a polynomial-time
computable `f` with `x ∈ L ↔ f x ∈ K`. -/
def PolyReducible (L K : Language) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ x, L x ↔ K (f x)

@[inherit_doc] scoped infix:50 " ≤p " => PolyReducible

/-- The proposition **P ≠ NP** (the open problem). -/
def PNeqNP : Prop := P ≠ NP

/-! ## Basic facts about the machine model -/

theorem Machine.run_add (M : Machine) (c : Cfg M.size) (a b : Nat) :
    M.run c (a + b) = (M.run c a).bind fun d => M.run d b := by
  induction a generalizing c with
  | zero => simp [Machine.run]
  | succ a ih =>
      have h1 : a + 1 + b = (a + b) + 1 := by omega
      rw [h1]
      cases h : M.step c with
      | none => simp [Machine.run, h]
      | some c' => simp [Machine.run, h, ih]

theorem Machine.run_of_halted (M : Machine) {c : Cfg M.size} (hc : M.step c = none) (n : Nat) :
    M.run c n = some c := by
  cases n with
  | zero => rfl
  | succ n => simp [Machine.run, hc]

/-- Halting configurations reached from a common start are unique. -/
theorem Machine.halting_unique (M : Machine) {c d e : Cfg M.size} {m n : Nat}
    (hm : M.run c m = some d) (hn : M.run c n = some e)
    (hd : M.step d = none) (he : M.step e = none) : d = e := by
  rcases Nat.le_total m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    rw [M.run_add, hm] at hn
    simp [M.run_of_halted hd k] at hn
    exact hn.symm
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    rw [M.run_add, hn] at hm
    simp [M.run_of_halted he k] at hm
    exact hm

/-- Every deterministic machine, viewed as a nondeterministic one. -/
def Machine.toNMachine (M : Machine) : NMachine where
  size := M.size
  start := M.start
  accept := M.accept
  next q s := (M.next q s).toList

@[simp] theorem Machine.toNMachine_size (M : Machine) : M.toNMachine.size = M.size := rfl

theorem Machine.toNMachine_step (M : Machine) (c : Cfg M.size) :
    M.toNMachine.step c = (M.step c).toList := by
  cases h : M.next c.state (c.tape c.head) <;>
    simp [NMachine.step, Machine.step, Machine.toNMachine, h]

theorem Machine.toNMachine_reaches (M : Machine) (c c' : Cfg M.size) (n : Nat) :
    M.toNMachine.reaches c n c' ↔ M.run c n = some c' := by
  induction n generalizing c with
  | zero =>
      constructor
      · rintro rfl; rfl
      · intro h; exact (Option.some.inj h)
  | succ n ih =>
      cases h : M.step c with
      | none => simp [NMachine.reaches, Machine.run, M.toNMachine_step, h]
      | some d => simp [NMachine.reaches, Machine.run, M.toNMachine_step, h, ih]

/-! ## P ⊆ NP -/

theorem P_subset_NP {L : Language} (hL : P L) : NP L := by
  obtain ⟨M, T, hT, hM⟩ := hL
  refine ⟨M.toNMachine, T, hT, fun x => ?_⟩
  have hinit : M.toNMachine.init x = M.init x := rfl
  constructor
  · intro hx
    obtain ⟨n, hn, c, hrun, hhalt, hacc⟩ := hM x
    refine ⟨n, hn, c, ?_, ?_, hacc.2 hx⟩
    · rw [hinit, M.toNMachine_reaches]; exact hrun
    · rw [M.toNMachine_step, hhalt]; rfl
  · rintro ⟨n, hn, c, hreach, hhalt, hacc⟩
    obtain ⟨m, _, d, hrun, hhaltd, hiff⟩ := hM x
    rw [hinit, M.toNMachine_reaches] at hreach
    rw [M.toNMachine_step] at hhalt
    have hc : M.step c = none := by
      cases h : M.step c with
      | none => rfl
      | some e => rw [h] at hhalt; simp [Option.toList] at hhalt
    have hcd : c = d := M.halting_unique hreach hrun hc hhaltd
    subst hcd
    exact hiff.1 hacc

/-! ## Polynomial-time reducibility is reflexive -/

/-- The machine that halts immediately, leaving its input untouched. -/
def idMachine : Machine where
  size := 1
  start := ⟨0, Nat.zero_lt_one⟩
  accept := fun _ => false
  next := fun _ _ => none

theorem polyTimeComputable_id : PolyTimeComputable id := by
  refine ⟨idMachine, fun _ => 0, ⟨0, 0, by simp⟩, fun x => ?_⟩
  refine ⟨0, Nat.le_refl 0, idMachine.init x, rfl, rfl, ?_⟩
  intro i hi
  simp [Machine.init, inputTape, hi]

theorem polyReducible_refl (L : Language) : L ≤p L :=
  ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-! ## The statement of the P vs NP problem -/

/-- **Statement of the P vs NP problem.**  With `P` and `NP` defined via time-bounded
deterministic and nondeterministic Turing machines as above, the assertion `P ≠ NP` is
equivalent to the existence of a language that is accepted in nondeterministic polynomial
time but is not decided in deterministic polynomial time.  (Whether this holds is the open
Millennium Problem; what is proved here is the equivalence of the two formulations, which
rests on `P ⊆ NP`.) -/
theorem P_vs_NP_statement : PNeqNP ↔ ∃ L : Language, NP L ∧ ¬ P L := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hcon
    apply h
    funext L
    apply propext
    constructor
    · exact fun hP => P_subset_NP hP
    · intro hNP
      apply Classical.byContradiction
      intro hP
      exact hcon ⟨L, hNP, hP⟩
  · rintro ⟨L, hNP, hP⟩ hEq
    exact hP (hEq ▸ hNP)

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

