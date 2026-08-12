import Mathlib

/-!
# The P vs NP statement

This file gives a self-contained formalization of the statement `P ≠ NP`, together with
all the definitions it depends on:

* single-tape deterministic Turing machines with a *finite* state set (`Frontier.Machine`)
  and their step-counted semantics (`Frontier.Machine.haltCfg`);
* nondeterministic single-tape Turing machines (`Frontier.NMachine`) and their
  time-bounded acceptance semantics (`Frontier.NMachine.AcceptsIn`);
* polynomially bounded time budgets (`Frontier.PolyBound`);
* the classes `Frontier.P` and `Frontier.NP` of languages over the binary alphabet;
* polynomial-time computable functions, polynomial-time many-one reducibility
  `Frontier.PolyReducible` (`≤ₚ`), `Frontier.NPHard` and `Frontier.NPComplete`;
* the statement itself, `Frontier.P_vs_NP_statement : Prop`.

The `P ≠ NP` question is open, so the statement is formalized as a `Prop` (a `def`), not
proved.  What *is* proved here are the sanity results: `P ⊆ NP`, the equivalent
formulation `P ≠ NP ↔ ∃ L ∈ NP, L ∉ P`, and reflexivity of `≤ₚ`.

Finiteness of the state set is essential: with an infinite state set one could smuggle the
answer into the transition function and every language would be decidable in linear time.
The tape alphabet is `Option Bool` (`none` = blank).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

/-- Words over the binary alphabet. -/
abbrev Word := List Bool

/-- A language is a set of binary words. -/
abbrev Language := Set Word

/-- Tape symbols: `none` is the blank symbol. -/
abbrev Sym := Option Bool

/-- Direction of a head move. -/
inductive Dir
  | left
  | right
  deriving DecidableEq, Repr

/-- A configuration of a machine with `n` states: the current state, the reversed tape
content strictly left of the head, the symbol under the head, and the tape content
strictly right of the head.  Cells not represented in the lists are blank. -/
structure Cfg (n : ℕ) where
  state : Fin n
  left : List Sym
  cur : Sym
  right : List Sym

namespace Cfg

/-- The output of a configuration: the symbols from the head position rightwards, up to
the first blank. -/
def output {n : ℕ} (c : Cfg n) : Word :=
  ((c.cur :: c.right).takeWhile Option.isSome).filterMap id

end Cfg

/-- Write symbol `s`, move in direction `d`, and enter state `q`. -/
def applyMove {n : ℕ} (q : Fin n) (s : Sym) (d : Dir) (c : Cfg n) : Cfg n :=
  match d with
  | Dir.left =>
      match c.left with
      | [] => ⟨q, [], none, s :: c.right⟩
      | a :: l => ⟨q, l, a, s :: c.right⟩
  | Dir.right =>
      match c.right with
      | [] => ⟨q, s :: c.left, none, []⟩
      | a :: r => ⟨q, s :: c.left, a, r⟩

/-- A deterministic single-tape Turing machine over the tape alphabet `Sym`, with the
finite state set `Fin size`.  `step q s = none` means the machine halts. -/
structure Machine where
  size : ℕ
  start : Fin size
  accept : Fin size → Bool
  step : Fin size → Sym → Option (Fin size × Sym × Dir)

namespace Machine

variable (M : Machine)

/-- One step of the machine, `none` if it has halted. -/
def stepCfg (c : Cfg M.size) : Option (Cfg M.size) :=
  (M.step c.state c.cur).map fun t => applyMove t.1 t.2.1 t.2.2 c

/-- The initial configuration on input `w`: the head scans the first letter of `w`. -/
def init (w : Word) : Cfg M.size := ⟨M.start, [], w.head?, w.tail.map some⟩

/-- `M.haltCfg t c` is the halting configuration reached from `c` within `t` steps, if the
machine does halt within that budget, and `none` otherwise. -/
def haltCfg : ℕ → Cfg M.size → Option (Cfg M.size)
  | 0, c => if (M.stepCfg c).isNone then some c else none
  | t + 1, c =>
      match M.stepCfg c with
      | none => some c
      | some c' => haltCfg t c'

/-- The bit output by `M` on input `w` when run for `T |w|` steps (`none` if it does not
halt in time). -/
def outcome (T : ℕ → ℕ) (w : Word) : Option Bool :=
  (M.haltCfg (T w.length) (M.init w)).map fun c => M.accept c.state

/-- `M` decides `L` within time `T`: on every input it halts within `T |w|` steps, and it
accepts exactly the words of `L`. -/
def Decides (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ w : Word, (M.outcome T w).isSome ∧ (M.outcome T w = some true ↔ w ∈ L)

/-- `M` computes the function `f` within time `T`: on input `w` it halts within `T |w|`
steps with `f w` written on the tape from the head position rightwards. -/
def Computes (f : Word → Word) (T : ℕ → ℕ) : Prop :=
  ∀ w : Word, ∃ c, M.haltCfg (T w.length) (M.init w) = some c ∧ c.output = f w

end Machine

/-- A nondeterministic single-tape Turing machine: `step q s` lists the available
transitions; the empty list means the machine halts. -/
structure NMachine where
  size : ℕ
  start : Fin size
  accept : Fin size → Bool
  step : Fin size → Sym → List (Fin size × Sym × Dir)

namespace NMachine

variable (N : NMachine)

/-- The initial configuration on input `w`. -/
def init (w : Word) : Cfg N.size := ⟨N.start, [], w.head?, w.tail.map some⟩

/-- One nondeterministic step. -/
def StepRel (c c' : Cfg N.size) : Prop :=
  ∃ t ∈ N.step c.state c.cur, c' = applyMove t.1 t.2.1 t.2.2 c

/-- A configuration is halted when no transition is available. -/
def Halted (c : Cfg N.size) : Prop := N.step c.state c.cur = []

/-- `N.ReachesIn k c c'` : `c'` is reachable from `c` by exactly `k` steps. -/
def ReachesIn : ℕ → Cfg N.size → Cfg N.size → Prop
  | 0, c, c' => c = c'
  | k + 1, c, c'' => ∃ c', N.StepRel c c' ∧ ReachesIn k c' c''

/-- `N` accepts `w` within time `T`: some computation path halts in an accepting state
after at most `T |w|` steps. -/
def AcceptsIn (T : ℕ → ℕ) (w : Word) : Prop :=
  ∃ k ≤ T w.length, ∃ c, N.ReachesIn k (N.init w) c ∧ N.Halted c ∧ N.accept c.state = true

/-- `N` decides `L` within time `T` in the nondeterministic sense: the words accepted by
some computation path of length at most `T |w|` are exactly those of `L`. -/
def NDecides (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ w : Word, N.AcceptsIn T w ↔ w ∈ L

end NMachine

/-- A time budget is polynomially bounded if it is dominated by `c * (n + 1) ^ k`. -/
def PolyBound (T : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n : ℕ, T n ≤ c * (n + 1) ^ k

/-- `L` is decidable in deterministic polynomial time. -/
def InP (L : Language) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ), PolyBound T ∧ M.Decides L T

/-- `L` is decidable in nondeterministic polynomial time. -/
def InNP (L : Language) : Prop :=
  ∃ (N : NMachine) (T : ℕ → ℕ), PolyBound T ∧ N.NDecides L T

/-- The complexity class `P`. -/
def P : Set Language := {L | InP L}

/-- The complexity class `NP`. -/
def NP : Set Language := {L | InNP L}

/-- A function on words is computable in deterministic polynomial time. -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ), PolyBound T ∧ M.Computes f T

/-- Polynomial-time many-one (Karp) reducibility. -/
def PolyReducible (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTimeComputable f ∧ ∀ w : Word, w ∈ A ↔ f w ∈ B

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyReducible

/-- `L` is NP-hard for polynomial-time many-one reducibility. -/
def NPHard (L : Language) : Prop := ∀ A ∈ NP, A ≤ₚ L

/-- `L` is NP-complete. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-- **The P versus NP statement**: the class of languages decidable in deterministic
polynomial time differs from the class of languages decidable in nondeterministic
polynomial time. -/
def P_vs_NP_statement : Prop := P ≠ NP

/-! ### Sanity results -/

namespace Machine

variable (M : Machine)

theorem haltCfg_of_stepCfg_none {c : Cfg M.size} (h : M.stepCfg c = none) (t : ℕ) :
    M.haltCfg t c = some c := by
  cases t with
  | zero => simp [haltCfg, h]
  | succ t => simp [haltCfg, h]

/-- The nondeterministic machine simulating a deterministic one. -/
def toNMachine : NMachine where
  size := M.size
  start := M.start
  accept := M.accept
  step := fun q s => (M.step q s).toList

@[simp] theorem toNMachine_size : M.toNMachine.size = M.size := rfl

theorem toNMachine_init (w : Word) : M.toNMachine.init w = M.init w := rfl

theorem halted_of_stepCfg_none {c : Cfg M.size} (h : M.stepCfg c = none) :
    M.toNMachine.Halted c := by
  simp only [NMachine.Halted, toNMachine, Option.toList_eq_nil_iff]
  rcases hstep : M.step c.state c.cur with _ | tr
  · rfl
  · rw [stepCfg, hstep] at h; simp at h

theorem stepRel_of_stepCfg {c d : Cfg M.size} (h : M.stepCfg c = some d) :
    M.toNMachine.StepRel c d := by
  rcases hstep : M.step c.state c.cur with _ | tr
  · rw [stepCfg, hstep] at h; simp at h
  · refine ⟨tr, ?_, ?_⟩
    · simp [toNMachine, hstep]
    · rw [stepCfg, hstep] at h
      simpa using h.symm

theorem stepCfg_of_stepRel {c d : Cfg M.size} (h : M.toNMachine.StepRel c d) :
    M.stepCfg c = some d := by
  obtain ⟨tr, htr, hd⟩ := h
  simp only [toNMachine, Option.mem_toList] at htr
  simp [stepCfg, htr, hd]

theorem reachesIn_of_haltCfg :
    ∀ (t : ℕ) (c c' : Cfg M.size), M.haltCfg t c = some c' →
      ∃ k ≤ t, M.toNMachine.ReachesIn k c c' ∧ M.toNMachine.Halted c' := by
  intro t
  induction t with
  | zero =>
      intro c c' h
      simp only [haltCfg] at h
      rcases hs : M.stepCfg c with _ | d
      · rw [hs] at h
        simp only [Option.isNone_none, if_true, Option.some.injEq] at h
        exact ⟨0, le_rfl, h, h ▸ M.halted_of_stepCfg_none hs⟩
      · rw [hs] at h; simp at h
  | succ t ih =>
      intro c c' h
      simp only [haltCfg] at h
      rcases hs : M.stepCfg c with _ | d
      · rw [hs] at h
        simp only [Option.some.injEq] at h
        exact ⟨0, Nat.zero_le _, h, h ▸ M.halted_of_stepCfg_none hs⟩
      · rw [hs] at h
        obtain ⟨k, hk, hreach, hhalt⟩ := ih d c' h
        exact ⟨k + 1, Nat.succ_le_succ hk, ⟨d, M.stepRel_of_stepCfg hs, hreach⟩, hhalt⟩

theorem haltCfg_of_reachesIn :
    ∀ (k t : ℕ) (c c' : Cfg M.size), k ≤ t → M.toNMachine.ReachesIn k c c' →
      M.toNMachine.Halted c' → M.haltCfg t c = some c' := by
  intro k
  induction k with
  | zero =>
      intro t c c' _ hreach hhalt
      simp only [NMachine.ReachesIn] at hreach
      subst hreach
      refine M.haltCfg_of_stepCfg_none ?_ t
      simp only [NMachine.Halted, toNMachine, Option.toList_eq_nil_iff] at hhalt
      simp [stepCfg, hhalt]
  | succ k ih =>
      intro t c c' hk hreach hhalt
      obtain ⟨d, hstep, hrest⟩ := hreach
      cases t with
      | zero => exact absurd hk (by omega)
      | succ t =>
          have hs : M.stepCfg c = some d := M.stepCfg_of_stepRel hstep
          simp only [haltCfg, hs]
          exact ih t d c' (by omega) hrest hhalt

end Machine

theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨M, T, hpoly, hdec⟩
  refine ⟨M.toNMachine, T, hpoly, ?_⟩
  intro w
  obtain ⟨-, hiff⟩ := hdec w
  constructor
  · rintro ⟨k, hk, c, hreach, hhalt, hacc⟩
    rw [← hiff]
    have hhc : M.haltCfg (T w.length) (M.init w) = some c :=
      M.haltCfg_of_reachesIn k (T w.length) (M.init w) c hk
        (by rwa [Machine.toNMachine_init] at hreach) hhalt
    simp only [Machine.outcome, hhc, Option.map_some, Option.some.injEq]
    exact hacc
  · intro hw
    have h1 : M.outcome T w = some true := hiff.mpr hw
    rcases hh : M.haltCfg (T w.length) (M.init w) with _ | c
    · simp [Machine.outcome, hh] at h1
    · obtain ⟨k, hk, hreach, hhalt⟩ := M.reachesIn_of_haltCfg (T w.length) (M.init w) c hh
      refine ⟨k, hk, c, by rwa [Machine.toNMachine_init], hhalt, ?_⟩
      simp only [Machine.outcome, hh, Option.map_some, Option.some.injEq] at h1
      exact h1

/-- `P ≠ NP` is equivalent to the existence of a language in `NP` but not in `P`. -/
theorem P_vs_NP_statement_iff :
    P_vs_NP_statement ↔ ∃ L : Language, L ∈ NP ∧ L ∉ P := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h (Set.Subset.antisymm P_subset_NP fun L hL => hcon L hL)
  · rintro ⟨L, hNP, hP⟩ h
    exact hP (h ▸ hNP)

/-! ### Basic facts about polynomial-time reducibility -/

/-- A one-state machine that halts immediately, leaving its input on the tape. -/
def idMachine : Machine where
  size := 1
  start := 0
  accept := fun _ => false
  step := fun _ _ => none

theorem idMachine_output (w : Word) : (idMachine.init w).output = w := by
  simp only [Machine.init, Cfg.output, idMachine]
  cases w with
  | nil => simp
  | cons b w =>
      simp only [List.head?, List.tail]
      induction w with
      | nil => simp
      | cons a w ihw => simpa using ihw

/-- The identity function is polynomial-time computable. -/
theorem polyTimeComputable_id : PolyTimeComputable id := by
  refine ⟨idMachine, fun _ => 0, ⟨0, 0, by simp⟩, fun w => ⟨idMachine.init w, ?_, ?_⟩⟩
  · simp [Machine.haltCfg, Machine.stepCfg, idMachine]
  · simpa using idMachine_output w

theorem PolyReducible.refl (A : Language) : A ≤ₚ A :=
  ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-! ### A worked example: the classes are non-vacuous

The definitions above are not vacuous: here is a concrete two-state machine deciding the
language of words whose first letter is `true`, witnessing that this language lies in `P`
(and hence in `NP`). -/

/-- The language of words whose first letter is `true`. -/
def FirstBitTrue : Language := {w | w.head? = some true}

/-- A two-state machine: from the start state `0` it moves right into the accepting state
`1` when it reads `true`, and halts (rejecting) otherwise. -/
def firstBitMachine : Machine where
  size := 2
  start := 0
  accept := fun q => q = 1
  step := fun q s => if q = 0 ∧ s = some true then some (1, some true, Dir.right) else none

theorem firstBitMachine_decides : firstBitMachine.Decides FirstBitTrue (fun _ => 1) := by
  intro w
  match w with
  | [] => constructor <;> simp [Machine.outcome, Machine.haltCfg, Machine.stepCfg, Machine.init,
      firstBitMachine, FirstBitTrue]
  | false :: rest => constructor <;> simp [Machine.outcome, Machine.haltCfg, Machine.stepCfg,
      Machine.init, firstBitMachine, FirstBitTrue]
  | true :: [] => constructor <;> simp [Machine.outcome, Machine.haltCfg, Machine.stepCfg,
      Machine.init, firstBitMachine, FirstBitTrue, applyMove]
  | true :: _ :: _ => constructor <;> simp [Machine.outcome, Machine.haltCfg, Machine.stepCfg,
      Machine.init, firstBitMachine, FirstBitTrue, applyMove]

theorem firstBitTrue_mem_P : FirstBitTrue ∈ P :=
  ⟨firstBitMachine, fun _ => 1, ⟨1, 0, by simp⟩, firstBitMachine_decides⟩

theorem firstBitTrue_mem_NP : FirstBitTrue ∈ NP := P_subset_NP firstBitTrue_mem_P

end Frontier

import Mathlib
import RequestProject.Frontier

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

