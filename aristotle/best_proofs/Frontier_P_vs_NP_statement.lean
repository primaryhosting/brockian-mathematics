import Mathlib

/-!
# The P vs NP statement

This file gives a self-contained formalization of the statement `P ≠ NP`, built from
scratch on top of a concrete Turing machine model:

* `Frontier.DTM`   : deterministic single-tape Turing machines over the alphabet `Option Bool`
                     (`none` is the blank symbol), with a finite state set;
* `Frontier.NTM`   : the nondeterministic variant;
* `Frontier.P`     : languages decided by a deterministic machine in polynomial time;
* `Frontier.NP`    : languages accepted by a nondeterministic machine in polynomial time;
* `Frontier.PolyTimeComputable`, `Frontier.PolyReducible` (`≤p`) : polynomial-time computable
  functions and polynomial-time many-one reducibility, together with `Frontier.NPHard` and
  `Frontier.NPComplete`;
* `Frontier.P_vs_NP_statement` : the proposition `P ≠ NP`.

`P_vs_NP_statement` is the famous open problem, so it is *stated*, not proved here.  What is
proved here are the basic structural facts that make the statement meaningful: `P ⊆ NP`,
the fact that `P ≠ NP` is equivalent to the existence of a language in `NP \ P`,
reflexivity of `≤p`, and the fact that the trivial languages are in `P` (so the definitions
are not vacuous).
-/

namespace Frontier

/-! ## Words, languages, tapes -/

/-- Words are finite binary strings. -/
abbrev Word := List Bool

/-- A language is a set of words. -/
abbrev Language := Set Word

/-- The tape alphabet: `none` is the blank symbol. -/
abbrev Alphabet := Option Bool

/-- A tape is a bi-infinite sequence of tape symbols. -/
abbrev Tape := ℤ → Alphabet

/-- Directions the head can move in one step. -/
inductive Dir
  | left
  | right
  | stay
  deriving DecidableEq, Fintype

/-- Moving a head position in a given direction. -/
def Dir.move : Dir → ℤ → ℤ
  | .left, i => i - 1
  | .right, i => i + 1
  | .stay, i => i

/-- The tape holding the word `x` in cells `0, 1, …, x.length - 1`, blank everywhere else. -/
def tapeOf (x : Word) : Tape := fun i => if 0 ≤ i then x[i.toNat]? else none

/-- A configuration of a machine with state set `Q`: the current state, the head position and
the tape contents. -/
structure Config (Q : Type) where
  state : Q
  head : ℤ
  tape : Tape

/-- Writing a symbol at the head position. -/
def writeAt (t : Tape) (i : ℤ) (a : Alphabet) : Tape := fun j => if j = i then a else t j

/-- The starting configuration on input `x`: state `q`, head on cell `0`, input on the tape. -/
def initConfig {Q : Type} (q : Q) (x : Word) : Config Q := ⟨q, 0, tapeOf x⟩

/-! ## Deterministic machines -/

/-- A deterministic single-tape Turing machine with state set `Q`.  The states `accept` and
`reject` are distinct halting states: the transition function fixes them (and leaves the tape
and the head alone), so that once the machine has accepted or rejected it stays there. -/
structure DTM (Q : Type) where
  /-- The initial state. -/
  start : Q
  /-- The accepting halting state. -/
  accept : Q
  /-- The rejecting halting state. -/
  reject : Q
  /-- The transition function: new state, symbol written, head movement. -/
  step : Q → Alphabet → Q × Alphabet × Dir
  /-- `accept` and `reject` really are different states. -/
  accept_ne_reject : accept ≠ reject
  /-- `accept` is a halting state. -/
  step_accept : ∀ a, step accept a = (accept, a, Dir.stay)
  /-- `reject` is a halting state. -/
  step_reject : ∀ a, step reject a = (reject, a, Dir.stay)

namespace DTM

variable {Q : Type} (M : DTM Q)

/-- One computation step of a deterministic machine. -/
def stepConfig (c : Config Q) : Config Q :=
  let tr := M.step c.state (c.tape c.head)
  ⟨tr.1, tr.2.2.move c.head, writeAt c.tape c.head tr.2.1⟩

/-- The configuration reached after `t` steps. -/
def run (t : ℕ) (c : Config Q) : Config Q := M.stepConfig^[t] c

/-- `M` accepts `x` within `t` steps. -/
def AcceptsIn (x : Word) (t : ℕ) : Prop :=
  ∃ s ≤ t, (M.run s (initConfig M.start x)).state = M.accept

/-- `M` halts on `x` within `t` steps. -/
def HaltsIn (x : Word) (t : ℕ) : Prop :=
  ∃ s ≤ t, (M.run s (initConfig M.start x)).state = M.accept ∨
    (M.run s (initConfig M.start x)).state = M.reject

/-- `M` decides the language `L` within the time bound `f` (a function of the input length):
on every input it halts within `f |x|` steps, and it accepts exactly the words of `L`. -/
def DecidesInTime (L : Language) (f : ℕ → ℕ) : Prop :=
  ∀ x : Word, M.HaltsIn x (f x.length) ∧ (M.AcceptsIn x (f x.length) ↔ x ∈ L)

/-- `M` computes the function `g` within the time bound `f`: on input `x` it reaches its
accepting (halting) state within `f |x|` steps, with the head back on cell `0` and the tape
containing exactly `g x`. -/
def ComputesInTime (g : Word → Word) (f : ℕ → ℕ) : Prop :=
  ∀ x : Word, ∃ s ≤ f x.length,
    (M.run s (initConfig M.start x)).state = M.accept ∧
    (M.run s (initConfig M.start x)).head = 0 ∧
    (M.run s (initConfig M.start x)).tape = tapeOf (g x)

end DTM

/-! ## Nondeterministic machines -/

/-- A nondeterministic single-tape Turing machine with state set `Q`.  `step q a` is the set of
allowed transitions.  Acceptance is by reaching the state `accept`. -/
structure NTM (Q : Type) where
  /-- The initial state. -/
  start : Q
  /-- The accepting state. -/
  accept : Q
  /-- The transition relation: the set of allowed (new state, written symbol, movement) triples. -/
  step : Q → Alphabet → Set (Q × Alphabet × Dir)

namespace NTM

variable {Q : Type} (N : NTM Q)

/-- One computation step of a nondeterministic machine. -/
def Step (c c' : Config Q) : Prop :=
  ∃ tr ∈ N.step c.state (c.tape c.head),
    c' = ⟨tr.1, tr.2.2.move c.head, writeAt c.tape c.head tr.2.1⟩

/-- `ReachesIn N t c c'` : the configuration `c'` is reachable from `c` in exactly `t` steps. -/
inductive ReachesIn : ℕ → Config Q → Config Q → Prop
  | refl (c : Config Q) : ReachesIn 0 c c
  | tail {t : ℕ} {c c' c'' : Config Q} :
      ReachesIn t c c' → N.Step c' c'' → ReachesIn (t + 1) c c''

/-- `N` accepts `x` within `t` steps: some computation path of length at most `t` starting from
the initial configuration reaches the accepting state. -/
def AcceptsIn (x : Word) (t : ℕ) : Prop :=
  ∃ s ≤ t, ∃ c : Config Q, N.ReachesIn s (initConfig N.start x) c ∧ c.state = N.accept

/-- `N` accepts exactly the language `L`, within the time bound `f`. -/
def AcceptsInTime (L : Language) (f : ℕ → ℕ) : Prop :=
  ∀ x : Word, x ∈ L ↔ N.AcceptsIn x (f x.length)

end NTM

/-! ## The classes P and NP, and polynomial-time reducibility -/

/-- The class `P`: languages decided by a deterministic Turing machine with finitely many states
in polynomial time. -/
def P : Set Language :=
  {L | ∃ (Q : Type) (_ : Fintype Q) (M : DTM Q) (c k : ℕ),
        M.DecidesInTime L (fun n => c * (n + 1) ^ k)}

/-- The class `NP`: languages accepted by a nondeterministic Turing machine with finitely many
states in polynomial time. -/
def NP : Set Language :=
  {L | ∃ (Q : Type) (_ : Fintype Q) (N : NTM Q) (c k : ℕ),
        N.AcceptsInTime L (fun n => c * (n + 1) ^ k)}

/-- A function on words is polynomial-time computable if some deterministic machine with finitely
many states computes it within a polynomial time bound. -/
def PolyTimeComputable (g : Word → Word) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (M : DTM Q) (c k : ℕ),
    M.ComputesInTime g (fun n => c * (n + 1) ^ k)

/-- Polynomial-time many-one reducibility: `A ≤p B` iff there is a polynomial-time computable
function `g` with `x ∈ A ↔ g x ∈ B` for all words `x`. -/
def PolyReducible (A B : Language) : Prop :=
  ∃ g : Word → Word, PolyTimeComputable g ∧ ∀ x : Word, x ∈ A ↔ g x ∈ B

@[inherit_doc] scoped infix:50 " ≤p " => PolyReducible

/-- A language is `NP`-hard if every language in `NP` reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ A ∈ NP, A ≤p L

/-- A language is `NP`-complete if it lies in `NP` and is `NP`-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-- **The P vs NP problem.**  The statement that the class of languages decidable in
deterministic polynomial time differs from the class of languages accepted in nondeterministic
polynomial time. -/
def P_vs_NP_statement : Prop := P ≠ NP

/-! ## Basic facts about the model -/

namespace DTM

variable {Q : Type} (M : DTM Q)

@[simp] theorem run_zero (c : Config Q) : M.run 0 c = c := rfl

theorem run_succ (t : ℕ) (c : Config Q) : M.run (t + 1) c = M.stepConfig (M.run t c) :=
  Function.iterate_succ_apply' _ _ _

/-- Once a deterministic machine has entered a halting state it stays there. -/
theorem run_state_persist {q : Q} (hq : ∀ a, M.step q a = (q, a, Dir.stay))
    {c : Config Q} {s s' : ℕ} (hss : s ≤ s') (h : (M.run s c).state = q) :
    (M.run s' c).state = q := by
  induction s', hss using Nat.le_induction with
  | base => exact h
  | succ n _ ih =>
    rw [M.run_succ, DTM.stepConfig]
    simp only [ih, hq]

end DTM

/-- The nondeterministic simulation of a deterministic machine. -/
def DTM.toNTM {Q : Type} (M : DTM Q) : NTM Q where
  start := M.start
  accept := M.accept
  step q a := {M.step q a}

theorem DTM.toNTM_step_iff {Q : Type} (M : DTM Q) (c c' : Config Q) :
    M.toNTM.Step c c' ↔ c' = M.stepConfig c := by
  constructor
  · rintro ⟨tr, htr, rfl⟩
    simp only [DTM.toNTM, Set.mem_singleton_iff] at htr
    subst htr
    rfl
  · rintro rfl
    exact ⟨M.step c.state (c.tape c.head), rfl, rfl⟩

theorem DTM.toNTM_reachesIn_iff {Q : Type} (M : DTM Q) (t : ℕ) (c c' : Config Q) :
    M.toNTM.ReachesIn t c c' ↔ c' = M.run t c := by
  induction t generalizing c' with
  | zero =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact NTM.ReachesIn.refl _
  | succ t ih =>
    constructor
    · intro h
      cases h with
      | tail hr hs =>
        rename_i c₁
        have h1 : c₁ = M.run t c := (ih c₁).1 hr
        have h2 : c' = M.stepConfig c₁ := (M.toNTM_step_iff _ _).1 hs
        rw [h2, h1, M.run_succ]
    · rintro rfl
      refine NTM.ReachesIn.tail ((ih (M.run t c)).2 rfl) ?_
      rw [M.toNTM_step_iff, M.run_succ]

theorem DTM.toNTM_acceptsIn_iff {Q : Type} (M : DTM Q) (x : Word) (t : ℕ) :
    M.toNTM.AcceptsIn x t ↔ M.AcceptsIn x t := by
  constructor
  · rintro ⟨s, hs, c, hc, hstate⟩
    refine ⟨s, hs, ?_⟩
    have : c = M.run s (initConfig M.start x) := (M.toNTM_reachesIn_iff _ _ _).1 hc
    rw [← this]
    exact hstate
  · rintro ⟨s, hs, hstate⟩
    exact ⟨s, hs, M.run s (initConfig M.start x),
      (M.toNTM_reachesIn_iff _ _ _).2 rfl, hstate⟩

/-- Every language decidable in deterministic polynomial time is accepted in nondeterministic
polynomial time: `P ⊆ NP`. -/
theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨Q, hQ, M, c, k, hM⟩
  refine ⟨Q, hQ, M.toNTM, c, k, ?_⟩
  intro x
  rw [DTM.toNTM_acceptsIn_iff]
  exact ((hM x).2).symm

/-- `P ≠ NP` is equivalent to the existence of a language in `NP` that is not in `P`. -/
theorem P_vs_NP_statement_iff :
    P_vs_NP_statement ↔ ∃ L : Language, L ∈ NP ∧ L ∉ P := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h (Set.Subset.antisymm P_subset_NP (fun L hL => hcon L hL))
  · rintro ⟨L, hNP, hP⟩ h
    exact hP (h ▸ hNP)

/-- Swapping the accepting and rejecting states of a deterministic machine. -/
def DTM.swap {Q : Type} (M : DTM Q) : DTM Q where
  start := M.start
  accept := M.reject
  reject := M.accept
  step := M.step
  accept_ne_reject := M.accept_ne_reject.symm
  step_accept := M.step_reject
  step_reject := M.step_accept

/-- The class `P` is closed under complementation. -/
theorem compl_mem_P {L : Language} (hL : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨Q, hQ, M, c, k, hM⟩ := hL
  refine ⟨Q, hQ, M.swap, c, k, ?_⟩
  intro x
  obtain ⟨⟨s, hs, hstate⟩, hiff⟩ := hM x
  have hrun : ∀ t : ℕ, (M.swap.run t (initConfig M.swap.start x))
      = M.run t (initConfig M.start x) := fun _ => rfl
  refine ⟨⟨s, hs, hstate.symm⟩, ?_⟩
  simp only [DTM.AcceptsIn, hrun, Set.mem_compl_iff]
  constructor
  · rintro ⟨s₁, hs₁, hrej⟩ hxL
    obtain ⟨s₂, hs₂, hacc⟩ := hiff.2 hxL
    have h₁ : (M.run (max s₁ s₂) (initConfig M.start x)).state = M.reject :=
      M.run_state_persist M.step_reject (le_max_left _ _) hrej
    have h₂ : (M.run (max s₁ s₂) (initConfig M.start x)).state = M.accept :=
      M.run_state_persist M.step_accept (le_max_right _ _) hacc
    exact M.accept_ne_reject (h₂ ▸ h₁)
  · intro hxL
    rcases hstate with hacc | hrej
    · exact absurd (hiff.1 ⟨s, hs, hacc⟩) hxL
    · exact ⟨s, hs, hrej⟩

/-! ## The definitions are not vacuous -/

/-- A two-state machine that never moves and never changes the tape; `q = true` is the accepting
state and `q = false` the rejecting one, and `b` is chosen as the starting state. -/
def trivialDTM (b : Bool) : DTM Bool where
  start := b
  accept := true
  reject := false
  step q a := (q, a, Dir.stay)
  accept_ne_reject := by decide
  step_accept := fun _ => rfl
  step_reject := fun _ => rfl

theorem trivialDTM_run_state (b : Bool) (t : ℕ) (c : Config Bool) :
    ((trivialDTM b).run t c).state = c.state := by
  induction t with
  | zero => rfl
  | succ t ih => rw [DTM.run_succ, DTM.stepConfig]; exact ih

/-- The language of all words is in `P`. -/
theorem univ_mem_P : (Set.univ : Language) ∈ P := by
  refine ⟨Bool, inferInstance, trivialDTM true, 0, 0, ?_⟩
  intro x
  refine ⟨⟨0, Nat.zero_le _, Or.inl ?_⟩, ?_⟩
  · rw [trivialDTM_run_state]; rfl
  · simp only [Set.mem_univ, iff_true]
    exact ⟨0, Nat.zero_le _, by rw [trivialDTM_run_state]; rfl⟩

/-- The empty language is in `P`. -/
theorem empty_mem_P : (∅ : Language) ∈ P := by
  refine ⟨Bool, inferInstance, trivialDTM false, 0, 0, ?_⟩
  intro x
  refine ⟨⟨0, Nat.zero_le _, Or.inr ?_⟩, ?_⟩
  · rw [trivialDTM_run_state]; rfl
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, -, hs⟩
    rw [trivialDTM_run_state] at hs
    exact Bool.noConfusion hs

/-- The language of all words is in `NP`. -/
theorem univ_mem_NP : (Set.univ : Language) ∈ NP := P_subset_NP univ_mem_P

/-- The empty language is in `NP`. -/
theorem empty_mem_NP : (∅ : Language) ∈ NP := P_subset_NP empty_mem_P

/-- The identity function is polynomial-time computable. -/
theorem polyTimeComputable_id : PolyTimeComputable (fun x : Word => x) := by
  refine ⟨Bool, inferInstance, trivialDTM true, 0, 0, ?_⟩
  intro x
  exact ⟨0, Nat.zero_le _, rfl, rfl, rfl⟩

/-- Polynomial-time reducibility is reflexive. -/
theorem polyReducible_refl (A : Language) : A ≤p A :=
  ⟨fun x => x, polyTimeComputable_id, fun _ => Iff.rfl⟩

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

