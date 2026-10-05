import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Overview

We give a self-contained formalization of the classes `P` and `NP` in terms of
time-bounded (nondeterministic) Turing machines over the alphabet `Bool`, together with
polynomial-time many-one reducibility and NP-completeness.

The headline declaration `Frontier.P_vs_NP_statement` records the precise content of the
`P ≠ NP` question: the classes differ exactly when some language is verifiable in
nondeterministic polynomial time but not decidable in deterministic polynomial time.
(The nontrivial content of this equivalence is the inclusion `P ⊆ NP`, proved below as
`Frontier.P_subset_NP`.)  The truth value of `P ≠ NP` itself is, of course, open; what is
formalized and proved here is the statement together with all of its definitions.
-/

namespace Frontier

/-! ## Tapes and machines -/

/-- Head movements of a Turing machine. -/
inductive Move : Type
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- A two-way infinite tape: cells are indexed by `ℤ`, and `none` denotes a blank cell. -/
abbrev Tape : Type := ℤ → Option Bool

/-- A language is a set of finite binary strings. -/
abbrev Language : Type := Set (List Bool)

/-- A (possibly nondeterministic) Turing machine with state set `Q`.  The transition
relation `step q b q' b' m` says: in state `q`, reading `b`, the machine may move to state
`q'`, write `b'` on the current cell, and move the head according to `m`. -/
structure Machine (Q : Type) : Type where
  /-- The transition relation. -/
  step : Q → Option Bool → Q → Option Bool → Move → Prop
  /-- The initial state. -/
  start : Q
  /-- The accepting state. -/
  accept : Q

/-- A configuration: current state, head position and tape contents. -/
structure Config (Q : Type) : Type where
  /-- Current state. -/
  state : Q
  /-- Current head position. -/
  pos : ℤ
  /-- Current tape contents. -/
  tape : Tape

/-- Effect of a head movement on the head position. -/
def movePos : Move → ℤ → ℤ
  | Move.left, i => i - 1
  | Move.right, i => i + 1
  | Move.stay, i => i

/-- Overwrite the cell `i` of a tape with the symbol `b`. -/
def writeTape (t : Tape) (i : ℤ) (b : Option Bool) : Tape := fun j => if j = i then b else t j

/-- The tape holding the input string `x` in cells `0, 1, …, |x| - 1`, blank elsewhere. -/
def initTape (x : List Bool) : Tape := fun i => if 0 ≤ i then x[i.toNat]? else none

/-- One computation step of `M`. -/
def Machine.stepRel {Q : Type} (M : Machine Q) (c c' : Config Q) : Prop :=
  ∃ b : Option Bool, ∃ m : Move,
    M.step c.state (c.tape c.pos) c'.state b m ∧
      c'.pos = movePos m c.pos ∧ c'.tape = writeTape c.tape c.pos b

/-- The initial configuration of `M` on input `x`. -/
def Machine.initConfig {Q : Type} (M : Machine Q) (x : List Bool) : Config Q :=
  { state := M.start, pos := 0, tape := initTape x }

/-- `M.reachesIn n c c'` : the configuration `c'` is reachable from `c` in exactly `n` steps. -/
def Machine.reachesIn {Q : Type} (M : Machine Q) : ℕ → Config Q → Config Q → Prop
  | 0, c, c' => c = c'
  | (n + 1), c, c' => ∃ d : Config Q, M.stepRel c d ∧ M.reachesIn n d c'

/-- `M` accepts `x` within `t` steps: some computation path of length at most `t` starting
from the initial configuration on `x` reaches the accepting state. -/
def Machine.AcceptsIn {Q : Type} (M : Machine Q) (x : List Bool) (t : ℕ) : Prop :=
  ∃ n ≤ t, ∃ c : Config Q, M.reachesIn n (M.initConfig x) c ∧ c.state = M.accept

/-- `M` is deterministic: from each state and scanned symbol there is at most one successor. -/
def Machine.Deterministic {Q : Type} (M : Machine Q) : Prop :=
  ∀ (q : Q) (b : Option Bool) (q₁ : Q) (b₁ : Option Bool) (m₁ : Move)
    (q₂ : Q) (b₂ : Option Bool) (m₂ : Move),
    M.step q b q₁ b₁ m₁ → M.step q b q₂ b₂ m₂ → q₁ = q₂ ∧ b₁ = b₂ ∧ m₁ = m₂

/-! ## Polynomial time bounds -/

/-- A time bound `f : ℕ → ℕ` is polynomially bounded. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n : ℕ, f n ≤ c * (n + 1) ^ k

/-! ## The classes P and NP -/

/-- `NTIME`-style definition of `NP`: `L ∈ NP` iff there is a finite-state
(nondeterministic) Turing machine `M` and a polynomial time bound `f` such that a string `x`
belongs to `L` exactly when `M` has an accepting computation on `x` of length at most
`f |x|`. -/
def NP : Set Language :=
  { L : Language | ∃ (Q : Type) (_ : Finite Q) (M : Machine Q) (f : ℕ → ℕ),
      PolyBounded f ∧ ∀ x : List Bool, x ∈ L ↔ M.AcceptsIn x (f x.length) }

/-- `DTIME`-style definition of `P`: as for `NP`, but the machine is required to be
deterministic. -/
def P : Set Language :=
  { L : Language | ∃ (Q : Type) (_ : Finite Q) (M : Machine Q) (f : ℕ → ℕ),
      M.Deterministic ∧ PolyBounded f ∧ ∀ x : List Bool, x ∈ L ↔ M.AcceptsIn x (f x.length) }

/-! ## Polynomial-time computable functions and reducibility -/

/-- `M` computes the output `y` on input `x` within `t` steps: some computation path of
length at most `t` reaches the accepting (halting) state with the tape holding `y`. -/
def Machine.ComputesIn {Q : Type} (M : Machine Q) (x y : List Bool) (t : ℕ) : Prop :=
  ∃ n ≤ t, ∃ c : Config Q, M.reachesIn n (M.initConfig x) c ∧ c.state = M.accept ∧
    c.tape = initTape y

/-- `f : List Bool → List Bool` is computable in deterministic polynomial time. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Machine Q) (t : ℕ → ℕ),
    M.Deterministic ∧ PolyBounded t ∧ ∀ x : List Bool, M.ComputesIn x (f x) (t x.length)

/-- Polynomial-time many-one reducibility: `L₁ ≤p L₂`. -/
def PolyReducible (L₁ L₂ : Language) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ x : List Bool, x ∈ L₁ ↔ f x ∈ L₂

@[inherit_doc] infix:50 " ≤p " => PolyReducible

/-- `L` is NP-hard (with respect to polynomial-time many-one reductions). -/
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤p L

/-- `L` is NP-complete. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-! ## Basic facts -/

/-- A deterministic polynomial-time machine witnesses membership in `NP` as well. -/
theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨Q, hQ, M, f, -, hf, hL⟩
  exact ⟨Q, hQ, M, f, hf, hL⟩

/-- The machine with a single state, which is both initial and accepting, and which has no
transitions. -/
def trivialMachine : Machine Unit where
  step := fun _ _ _ _ _ => False
  start := ()
  accept := ()

/-- The machine with two states and no transitions, whose accepting state differs from its
initial state. -/
def rejectMachine : Machine Bool where
  step := fun _ _ _ _ _ => False
  start := false
  accept := true

theorem polyBounded_zero : PolyBounded (fun _ => 0) := ⟨0, 0, by simp⟩

/-- The set of all strings is decidable in polynomial time. -/
theorem univ_mem_P : (Set.univ : Language) ∈ P := by
  refine ⟨Unit, inferInstance, trivialMachine, fun _ => 0, ?_, polyBounded_zero, ?_⟩
  · rintro q b q₁ b₁ m₁ q₂ b₂ m₂ h -
    exact absurd h (by simp [trivialMachine])
  · intro x
    simp only [Set.mem_univ, true_iff]
    exact ⟨0, le_rfl, trivialMachine.initConfig x, rfl, rfl⟩

/-- The empty language is decidable in polynomial time. -/
theorem empty_mem_P : (∅ : Language) ∈ P := by
  refine ⟨Bool, inferInstance, rejectMachine, fun _ => 0, ?_, polyBounded_zero, ?_⟩
  · rintro q b q₁ b₁ m₁ q₂ b₂ m₂ h -
    exact absurd h (by simp [rejectMachine])
  · intro x
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨n, hn, c, hc, hacc⟩
    interval_cases n
    · cases hc
      exact Bool.false_ne_true hacc

/-- Polynomial-time reducibility is reflexive: the identity function is computable in
polynomial time. -/
theorem polyReducible_refl (L : Language) : L ≤p L := by
  refine ⟨id, ⟨Unit, inferInstance, trivialMachine, fun _ => 0, ?_, polyBounded_zero, ?_⟩,
    fun x => Iff.rfl⟩
  · rintro q b q₁ b₁ m₁ q₂ b₂ m₂ h -
    exact absurd h (by simp [trivialMachine])
  · intro x
    exact ⟨0, le_rfl, trivialMachine.initConfig x, rfl, rfl, rfl⟩

/-! ## The statement of the P vs NP problem -/

/--
**The P versus NP statement.**

With `P` and `NP` defined via time-bounded Turing machines as above, the assertion
`P ≠ NP` is equivalent to the existence of a language that can be recognized in
nondeterministic polynomial time but not in deterministic polynomial time.

This is the precise formalized content of the P vs NP question; its resolution is open.
-/
theorem P_vs_NP_statement : P ≠ NP ↔ ∃ L : Language, L ∈ NP ∧ L ∉ P := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h (Set.Subset.antisymm P_subset_NP fun L hL => hcon L hL)
  · rintro ⟨L, hNP, hP⟩ heq
    exact hP (heq ▸ hNP)

end Frontier

