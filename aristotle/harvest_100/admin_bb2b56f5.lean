/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file gives a precise, self-contained formalization of the statement
`P ≠ NP`, in terms of time-bounded (deterministic and nondeterministic)
one-tape Turing machines, together with polynomial-time many-one reducibility
and NP-completeness.

The file deliberately uses no imports beyond Lean's `Init`, so that the meaning
of the statement depends on nothing but the definitions given here.

The main theorem `Frontier.P_vs_NP_statement` records the equivalence between
the assertion `P ≠ NP` and the existence of a language lying in `NP` but not in
`P`.  (Whether that assertion is *true* is the open Millennium Problem; what is
proved here is the equivalence of the two formulations, which rests on the
inclusion `P ⊆ NP`, proved below as `Frontier.P_subset_NP`.)
-/

namespace Frontier

/-! ## Machine model

A one-tape Turing machine over the binary alphabet.  The tape is bi-infinite,
indexed by `ℤ`; a cell holds `some b` for a bit `b`, or `none` for the blank.
Nondeterminism is part of the model: the transition relation `next q a` may
relate a (state, scanned symbol) pair to any number of successor triples
(new state, symbol written, head move).  A machine is *deterministic* when each
such set of successors has at most one element.
-/

/-- A head move: left, stay, or right. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq

/-- The displacement of the head associated with a move. -/
def Move.delta : Move → Int
  | .left => -1
  | .stay => 0
  | .right => 1

/-- A tape symbol: `none` is the blank, `some b` is the bit `b`. -/
abbrev Symb := Option Bool

/-- A (possibly nondeterministic) one-tape Turing machine with state type `Q`.
Finiteness of the state type is imposed separately, where machines are used. -/
structure Machine (Q : Type) where
  /-- The initial state. -/
  start : Q
  /-- The accepting states. -/
  accept : Q → Prop
  /-- The transition relation: in state `q`, scanning symbol `a`, the machine may
  move to state `q'`, write `b`, and move its head according to `m`, for any
  `(q', b, m)` with `next q a (q', b, m)`. -/
  next : Q → Symb → (Q × Symb × Move) → Prop

/-- The state type `Q` is finite: it is covered by a list of length `n`. -/
def FiniteStates (Q : Type) : Prop :=
  ∃ (n : Nat) (e : Fin n → Q), ∀ q, ∃ i, e i = q

/-- A configuration: the current state, the tape contents, and the head
position. -/
structure Cfg (Q : Type) where
  /-- The current state. -/
  state : Q
  /-- The current tape contents. -/
  tape : Int → Symb
  /-- The current head position. -/
  pos : Int

/-- The tape holding the word `x` in cells `0, 1, …, |x| - 1` and blanks
elsewhere. -/
def tapeOf (x : List Bool) : Int → Symb :=
  fun i => if 0 ≤ i then x[i.toNat]? else none

/-- The initial configuration of `M` on input `x`: the start state, the input
written on an otherwise blank tape, and the head on cell `0`. -/
def initCfg {Q : Type} (M : Machine Q) (x : List Bool) : Cfg Q :=
  ⟨M.start, tapeOf x, 0⟩

/-- One computation step of `M`: read the scanned symbol, and according to the
transition relation change state, overwrite the scanned cell, and move the
head. -/
def Step {Q : Type} (M : Machine Q) (c c' : Cfg Q) : Prop :=
  ∃ q' b m, M.next c.state (c.tape c.pos) (q', b, m) ∧
    c' = ⟨q', fun j => if j = c.pos then b else c.tape j, c.pos + m.delta⟩

/-- `Steps M n c c'` says that `c'` is reachable from `c` by exactly `n`
computation steps of `M`. -/
def Steps {Q : Type} (M : Machine Q) : Nat → Cfg Q → Cfg Q → Prop
  | 0, c, c' => c = c'
  | (n + 1), c, c' => ∃ d, Step M c d ∧ Steps M n d c'

/-- A configuration is halted when no computation step is possible from it. -/
def Halted {Q : Type} (M : Machine Q) (c : Cfg Q) : Prop :=
  ∀ y, ¬ M.next c.state (c.tape c.pos) y

/-- `M` is deterministic: for each state and scanned symbol there is at most one
possible successor triple. -/
def Deterministic {Q : Type} (M : Machine Q) : Prop :=
  ∀ q a y z, M.next q a y → M.next q a z → y = z

/-- `M` accepts `x` within `t` steps: some computation of length at most `t`,
starting from the initial configuration on `x`, reaches an accepting state. -/
def AcceptsWithin {Q : Type} (M : Machine Q) (x : List Bool) (t : Nat) : Prop :=
  ∃ n, n ≤ t ∧ ∃ c, Steps M n (initCfg M x) c ∧ M.accept c.state

/-- `M` computes the word function `f` within `t` steps: on every input `x`,
some computation of length at most `t x` reaches a halted configuration whose
tape holds `f x` in cells `0, 1, …` and blanks elsewhere. -/
def ComputesWithin {Q : Type} (M : Machine Q) (f : List Bool → List Bool)
    (t : List Bool → Nat) : Prop :=
  ∀ x, ∃ n, n ≤ t x ∧ ∃ c, Steps M n (initCfg M x) c ∧ Halted M c ∧
    c.tape = tapeOf (f x)

/-! ## Polynomial time bounds -/

/-- The polynomial bound `c · (n + 1) ^ k`.  As `c` and `k` range over the
naturals these bounds are cofinal among all polynomials with natural
coefficients, so "bounded by some `polyBound c k`" is exactly "polynomially
bounded". -/
def polyBound (c k n : Nat) : Nat := c * (n + 1) ^ k

/-! ## The classes P and NP -/

/-- A language is a set of binary words, represented by its membership
predicate. -/
abbrev Language := List Bool → Prop

/-- `NP`: the languages `L` for which there is a nondeterministic Turing machine
`M` with finitely many states and a polynomial time bound such that `x ∈ L` if
and only if `M` has an accepting computation on `x` of length at most
`polyBound c k |x|`. -/
def NP : Language → Prop :=
  fun L => ∃ (Q : Type) (M : Machine Q) (c k : Nat), FiniteStates Q ∧
    ∀ x, L x ↔ AcceptsWithin M x (polyBound c k x.length)

/-- `P`: the languages `L` for which there is a *deterministic* Turing machine
`M` with finitely many states and a polynomial time bound such that `x ∈ L` if
and only if `M` accepts `x` within `polyBound c k |x|` steps. -/
def P : Language → Prop :=
  fun L => ∃ (Q : Type) (M : Machine Q) (c k : Nat), FiniteStates Q ∧
    Deterministic M ∧ ∀ x, L x ↔ AcceptsWithin M x (polyBound c k x.length)

/-! ## Polynomial-time reducibility -/

/-- A word function is polynomial-time computable when some deterministic
Turing machine with finitely many states computes it within a polynomial number
of steps. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (Q : Type) (M : Machine Q) (c k : Nat), FiniteStates Q ∧ Deterministic M ∧
    ComputesWithin M f (fun x => polyBound c k x.length)

/-- Polynomial-time many-one reducibility, `L ≤ₚ L'`: there is a polynomial-time
computable `f` with `x ∈ L ↔ f x ∈ L'`. -/
def ReducesTo (L L' : Language) : Prop :=
  ∃ f, PolyTimeComputable f ∧ ∀ x, L x ↔ L' (f x)

@[inherit_doc] scoped infix:50 " ≤ₚ " => ReducesTo

/-- `L` is NP-hard: every language in `NP` reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L', NP L' → L' ≤ₚ L

/-- `L` is NP-complete: it lies in `NP` and is NP-hard. -/
def NPComplete (L : Language) : Prop := NP L ∧ NPHard L

/-! ## Basic facts about the model -/

/-- Every language in `P` is in `NP`: a deterministic machine is in particular a
nondeterministic one. -/
theorem P_subset_NP : ∀ L, P L → NP L := by
  rintro L ⟨Q, M, c, k, hfin, -, h⟩
  exact ⟨Q, M, c, k, hfin, h⟩

/-- The one-state machine with no transitions and no accepting state. -/
def trivialMachine (acc : Prop) : Machine Unit where
  start := ()
  accept := fun _ => acc
  next := fun _ _ _ => False

theorem finiteStates_unit : FiniteStates Unit :=
  ⟨1, fun _ => (), fun _ => ⟨0, rfl⟩⟩

theorem deterministic_trivialMachine (acc : Prop) :
    Deterministic (trivialMachine acc) := by
  rintro q a y z ⟨⟩

/-- The identity function is polynomial-time computable: the one-state machine
with no transitions halts immediately, leaving its input on the tape. -/
theorem polyTimeComputable_id : PolyTimeComputable id := by
  refine ⟨Unit, trivialMachine False, 0, 0, finiteStates_unit,
    deterministic_trivialMachine False, ?_⟩
  intro x
  exact ⟨0, Nat.zero_le _, initCfg _ x, rfl, fun _ h => h, rfl⟩

/-- Polynomial-time reducibility is reflexive. -/
theorem reducesTo_refl (L : Language) : L ≤ₚ L :=
  ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- Sanity check: the empty language lies in `P`. -/
theorem empty_mem_P : P (fun _ => False) := by
  refine ⟨Unit, trivialMachine False, 0, 0, finiteStates_unit,
    deterministic_trivialMachine False, ?_⟩
  intro x
  constructor
  · exact fun h => h.elim
  · rintro ⟨n, -, c, -, hc⟩
    exact hc

/-- Sanity check: the language of all words lies in `P`. -/
theorem univ_mem_P : P (fun _ => True) := by
  refine ⟨Unit, trivialMachine True, 0, 0, finiteStates_unit,
    deterministic_trivialMachine True, ?_⟩
  intro x
  exact ⟨fun _ => ⟨0, Nat.zero_le _, initCfg _ x, rfl, trivial⟩, fun _ => trivial⟩

/-! ## The statement of the P versus NP problem -/

/-- The assertion `P ≠ NP`, with `P` and `NP` the classes defined above via
time-bounded deterministic, respectively nondeterministic, Turing machines. -/
def P_ne_NP : Prop := P ≠ NP

/-- **The P versus NP statement.**

With `P` and `NP` defined through time-bounded (deterministic, respectively
nondeterministic) one-tape Turing machines as above, the assertion `P ≠ NP` is
equivalent to the existence of a language that is decidable by a
polynomial-time nondeterministic machine but by no polynomial-time
deterministic machine.

Whether the assertion holds is the open Millennium Problem; what is proved here
is the equivalence of the two formulations, which rests on the inclusion
`P ⊆ NP` (`Frontier.P_subset_NP`). -/
theorem P_vs_NP_statement : P_ne_NP ↔ ∃ L, NP L ∧ ¬ P L := by
  constructor
  · intro h
    -- If no language separated the classes, the two classes would be equal.
    apply Classical.byContradiction
    intro hc
    apply h
    funext L
    apply propext
    refine ⟨P_subset_NP L, fun hL => ?_⟩
    by_cases hPL : P L
    · exact hPL
    · exact absurd ⟨L, hL, hPL⟩ hc
  · rintro ⟨L, hNP, hP⟩ hEq
    exact hP (hEq ▸ hNP)

end Frontier

