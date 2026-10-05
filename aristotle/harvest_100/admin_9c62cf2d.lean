/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained formalization of the P vs NP question in terms of time-bounded
(deterministic and nondeterministic) single-tape Turing machines and polynomial-time
many-one reducibility.

The development is elementary and depends on nothing beyond the Lean 4 prelude, so that
the file can literally begin with the header comment above.

Main declarations:

* `Frontier.Machine`             : single-tape Turing machine with finite control;
* `Frontier.AcceptsWithin`       : acceptance within a given number of steps;
* `Frontier.Deterministic`       : determinism of the transition relation;
* `Frontier.DecidesInPolyTime`   : deciding a language within a polynomial time bound;
* `Frontier.P`, `Frontier.NP`    : the two complexity classes;
* `Frontier.PolyReducible`       : polynomial-time many-one reducibility `≤ₚ`;
* `Frontier.NPComplete`          : NP-completeness;
* `Frontier.P_vs_NP_statement`   : the statement of the P vs NP problem, in the form
  `P ≠ NP ↔ ∃ L, L ∈ NP ∧ L ∉ P`.
-/

namespace Frontier

/-- Words are finite binary strings. -/
abbrev Word : Type := List Bool

/-- A language is a set of words, represented by its membership predicate. -/
abbrev Language : Type := Word → Prop

/-- The direction in which the tape head moves in one step. -/
inductive Dir : Type
  | left : Dir
  | right : Dir
  | stay : Dir

/-- The displacement of the head associated with a direction. -/
def Dir.delta : Dir → Int
  | Dir.left => -1
  | Dir.right => 1
  | Dir.stay => 0

/-- A (possibly nondeterministic) single-tape Turing machine: a finite set of control
states, an initial state, a set of accepting states, and a transition relation over the
tape alphabet `Option Bool`, where `none` is the blank symbol.

Finiteness of the control is expressed by exhibiting a list of states containing every
state. -/
structure Machine : Type 1 where
  /-- The type of control states. -/
  State : Type
  /-- A list enumerating the control states. -/
  states : List State
  /-- Every state occurs in the enumeration; this makes the control finite. -/
  states_complete : ∀ q : State, q ∈ states
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  final : State → Bool
  /-- `next q a q' w d` holds when, reading the symbol `a` in state `q`, the machine may
  move to state `q'`, write the symbol `w` and move the head in direction `d`. -/
  next : State → Option Bool → State → Option Bool → Dir → Prop

/-- A configuration of `M`: control state, head position, and tape contents. -/
structure Cfg (M : Machine) : Type where
  /-- The current control state. -/
  state : M.State
  /-- The current head position. -/
  head : Int
  /-- The current tape contents; `none` denotes a blank cell. -/
  tape : Int → Option Bool

/-- The tape holding the input word `x` in the cells `0, 1, …, |x| - 1`, blank elsewhere. -/
def initTape (x : Word) : Int → Option Bool :=
  fun i => if 0 ≤ i then x[i.toNat]? else none

/-- The initial configuration of `M` on input `x`: the initial state, the head on cell `0`
and the input written on the tape. -/
def initCfg (M : Machine) (x : Word) : Cfg M := ⟨M.start, 0, initTape x⟩

/-- One computation step of `M`. -/
def Step (M : Machine) (c c' : Cfg M) : Prop :=
  ∃ q' w d, M.next c.state (c.tape c.head) q' w d ∧
    c' = ⟨q', c.head + d.delta, fun i => if i = c.head then w else c.tape i⟩

/-- `StepN M n c c'` holds when `M` can pass from the configuration `c` to the
configuration `c'` in exactly `n` steps. -/
def StepN (M : Machine) : Nat → Cfg M → Cfg M → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c'', Step M c c'' ∧ StepN M n c'' c'

/-- `M` accepts the input `x` within `t` steps: some computation of length at most `t`,
started in the initial configuration on input `x`, reaches an accepting state. -/
def AcceptsWithin (M : Machine) (x : Word) (t : Nat) : Prop :=
  ∃ n, n ≤ t ∧ ∃ c : Cfg M, StepN M n (initCfg M x) c ∧ M.final c.state = true

/-- A machine is deterministic when each (state, scanned symbol) pair admits at most one
transition. -/
def Deterministic (M : Machine) : Prop :=
  ∀ (q : M.State) (a : Option Bool) (q₁ : M.State) (w₁ : Option Bool) (d₁ : Dir)
    (q₂ : M.State) (w₂ : Option Bool) (d₂ : Dir),
    M.next q a q₁ w₁ d₁ → M.next q a q₂ w₂ d₂ → q₁ = q₂ ∧ w₁ = w₂ ∧ d₁ = d₂

/-- `M` decides `L` in polynomial time: there are constants `c, k` such that a word `x`
belongs to `L` exactly when `M` accepts `x` within `c * |x| ^ k + c` steps. -/
def DecidesInPolyTime (M : Machine) (L : Language) : Prop :=
  ∃ c k : Nat, ∀ x : Word, L x ↔ AcceptsWithin M x (c * x.length ^ k + c)

/-- The class `P`: languages decided by a *deterministic* Turing machine within a
polynomial time bound. -/
def P : Language → Prop :=
  fun L => ∃ M : Machine, Deterministic M ∧ DecidesInPolyTime M L

/-- The class `NP`: languages decided by a *nondeterministic* Turing machine within a
polynomial time bound, i.e. membership in `L` is equivalent to the existence of an
accepting computation of polynomial length. -/
def NP : Language → Prop :=
  fun L => ∃ M : Machine, DecidesInPolyTime M L

/-! ### Polynomial-time computable functions and polynomial reducibility -/

/-- The tape `tape` holds the word `y` in the cells `0, 1, …, |y| - 1` and is blank
elsewhere. -/
def TapeEncodes (tape : Int → Option Bool) (y : Word) : Prop :=
  ∀ i : Int, tape i = if 0 ≤ i then y[i.toNat]? else none

/-- `M` computes the function `f` in polynomial time: `M` is deterministic and, on every
input `x`, reaches within `c * |x| ^ k + c` steps a final state whose tape holds `f x`. -/
def ComputesInPolyTime (M : Machine) (f : Word → Word) : Prop :=
  Deterministic M ∧
    ∃ c k : Nat, ∀ x : Word, ∃ n, n ≤ c * x.length ^ k + c ∧ ∃ cfg : Cfg M,
      StepN M n (initCfg M x) cfg ∧ M.final cfg.state = true ∧ TapeEncodes cfg.tape (f x)

/-- A function on words is polynomial-time computable when some deterministic machine
computes it within a polynomial time bound. -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  ∃ M : Machine, ComputesInPolyTime M f

/-- Polynomial-time many-one reducibility: `A ≤ₚ B` when there is a polynomial-time
computable `f` with `x ∈ A ↔ f x ∈ B`. -/
def PolyReducible (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTimeComputable f ∧ ∀ x : Word, A x ↔ B (f x)

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyReducible

/-- `L` is `NP`-hard: every language of `NP` reduces to `L` in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ A : Language, NP A → A ≤ₚ L

/-- `L` is `NP`-complete: it lies in `NP` and is `NP`-hard. -/
def NPComplete (L : Language) : Prop := NP L ∧ NPHard L

/-! ### Basic facts -/

/-- A deterministic machine is in particular a nondeterministic one, hence `P ⊆ NP`. -/
theorem P_subset_NP (L : Language) (h : P L) : NP L :=
  match h with
  | ⟨M, _, hd⟩ => ⟨M, hd⟩

/-- The machine with a single (non-accepting) state and no transitions. -/
def trivialMachine (acc : Bool) : Machine where
  State := Unit
  states := [()]
  states_complete := fun q => by cases q; exact List.Mem.head _
  start := ()
  final := fun _ => acc
  next := fun _ _ _ _ _ => False

/-- The empty language belongs to `P`. -/
theorem empty_mem_P : P (fun _ : Word => False) := by
  refine ⟨trivialMachine false, ?_, 0, 0, ?_⟩
  · intro q a q₁ w₁ d₁ q₂ w₂ d₂ h
    exact h.elim
  · intro x
    apply Iff.intro
    · intro h; exact h.elim
    · intro h
      match h with
      | ⟨n, _, cfg, _, hfin⟩ => exact Bool.noConfusion hfin

/-- The language of all words belongs to `P`. -/
theorem univ_mem_P : P (fun _ : Word => True) := by
  refine ⟨trivialMachine true, ?_, 0, 0, ?_⟩
  · intro q a q₁ w₁ d₁ q₂ w₂ d₂ h
    exact h.elim
  · intro x
    apply Iff.intro
    · intro _
      exact ⟨0, Nat.le_refl _, initCfg _ x, rfl, rfl⟩
    · intro _; trivial

/-- The identity function is polynomial-time computable: a machine that halts immediately
leaves its input on the tape. -/
theorem polyTimeComputable_id : PolyTimeComputable (fun x : Word => x) := by
  refine ⟨trivialMachine true, ?_, 0, 0, ?_⟩
  · intro q a q₁ w₁ d₁ q₂ w₂ d₂ h
    exact h.elim
  · intro x
    exact ⟨0, Nat.le_refl _, initCfg _ x, rfl, rfl, fun i => rfl⟩

/-- Polynomial-time reducibility is reflexive. -/
theorem polyReducible_refl (A : Language) : A ≤ₚ A :=
  ⟨fun x => x, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- If `P = NP`, then every `NP`-complete language is decidable in deterministic
polynomial time. -/
theorem NPComplete_mem_P_of_P_eq_NP (L : Language) (h : P = NP) (hL : NPComplete L) : P L :=
  h ▸ hL.1

/-- Conversely, exhibiting an `NP`-complete language outside `P` separates the two
classes. -/
theorem P_ne_NP_of_NPComplete_not_mem_P (L : Language) (hL : NPComplete L) (hP : ¬ P L) :
    P ≠ NP := fun h => hP (NPComplete_mem_P_of_P_eq_NP L h hL)

/-! ### The statement of the P vs NP problem -/

/-- **The P vs NP question.**

With `P` and `NP` defined through polynomial-time bounded deterministic and
nondeterministic single-tape Turing machines as above, the assertion `P ≠ NP` says
precisely that some language is decidable in nondeterministic polynomial time but not in
deterministic polynomial time.

(The separation itself is a famous open problem and is *not* proved here: what is proved
is that the formal statement `P ≠ NP` is equivalent to the existence of such a language,
which uses the inclusion `P ⊆ NP`.) -/
theorem P_vs_NP_statement : P ≠ NP ↔ ∃ L : Language, NP L ∧ ¬ P L := by
  apply Iff.intro
  · intro h
    apply Classical.byContradiction
    intro hc
    apply h
    funext L
    apply propext
    apply Iff.intro
    · intro hL
      exact P_subset_NP L hL
    · intro hL
      apply Classical.byContradiction
      intro hnp
      exact hc ⟨L, hL, hnp⟩
  · intro h he
    match h with
    | ⟨L, hNP, hP⟩ => exact hP (he ▸ hNP)

end Frontier

