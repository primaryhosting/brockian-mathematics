import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file gives a complete, self-contained formalization of the statement `P ≠ NP`.
(Lean 4 requires every `import` to come before any other command, including
module documentation, so the header block above sits just after the single
`import Mathlib` line.)

Everything is built from scratch:

* a deterministic single-tape Turing machine model (`Frontier.DTM`) with a
  two-way infinite tape indexed by `ℤ`, tape alphabet `Option Bool`
  (`none` = blank), distinguished `accept` and `reject` states which are
  absorbing, and a total one-step transition function;
* a nondeterministic machine model (`Frontier.NTM`) whose transitions form a
  relation;
* time-bounded computation (`Frontier.DTM.run`, `Frontier.NTM.ReachIn`) and
  polynomial time bounds (`Frontier.IsPolyBound`);
* the classes `Frontier.P` and `Frontier.NP` of languages over `{0,1}`;
* polynomial-time computable functions, polynomial-time many-one reducibility
  `≤p`, NP-hardness and NP-completeness;
* the statement itself, `Frontier.P_vs_NP_statement : Prop`, namely `P ≠ NP`.

Some sanity results are proved: `P ⊆ NP`, the reformulation of the statement as
"some NP language is not in P", reflexivity of `≤p`, and the membership of the
two trivial languages in `P` (so that the classes are not empty).

The statement `P ≠ NP` itself is, of course, the famous open problem and is not
proved here.
-/

namespace Frontier

/-! ## Words and languages -/

/-- A word is a finite binary string. -/
abbrev Word := List Bool

/-- A language is a set of binary strings. -/
abbrev Language := Set Word

/-- Tape symbols: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym := Option Bool

/-! ## Configurations -/

/-- A head movement. -/
inductive Move where
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- The effect of a head movement on a (two-way infinite) tape position. -/
def Move.apply : Move → ℤ → ℤ
  | .left, i => i - 1
  | .right, i => i + 1
  | .stay, i => i

/-- A configuration of a machine with state set `Fin n`: a current state, the
contents of the two-way infinite tape, and the position of the head. -/
structure Cfg (n : ℕ) where
  /-- The current control state. -/
  state : Fin n
  /-- The contents of the tape. -/
  tape : ℤ → Sym
  /-- The current position of the head. -/
  head : ℤ

/-- Write symbol `s` at position `i` of the tape `t`. -/
def writeTape (t : ℤ → Sym) (i : ℤ) (s : Sym) : ℤ → Sym :=
  fun j => if j = i then s else t j

/-- The initial tape holding the input word `x` at positions `0, 1, …`, all
other cells being blank. -/
def initTape (x : Word) : ℤ → Sym :=
  fun i => if i < 0 then none else x[i.toNat]?

/-! ## Deterministic machines -/

/-- A deterministic one-tape Turing machine with finitely many states
`Fin size`, working over the tape alphabet `Sym`. -/
structure DTM where
  /-- Number of control states. -/
  size : ℕ
  /-- The initial state. -/
  start : Fin size
  /-- The accepting state. -/
  accept : Fin size
  /-- The rejecting state. -/
  reject : Fin size
  /-- Transition function: from a state and the scanned symbol, produce the new
  state, the symbol to write, and the head movement. -/
  step : Fin size → Sym → Fin size × Sym × Move
  /-- The accepting and rejecting states are distinct. -/
  accept_ne_reject : accept ≠ reject

/-- A configuration is halted if its state is the accepting or the rejecting
state. -/
def DTM.Halted (M : DTM) (c : Cfg M.size) : Prop :=
  c.state = M.accept ∨ c.state = M.reject

/-- One step of the machine. Halting configurations are fixed points, so that
acceptance and rejection are absorbing. -/
def DTM.stepCfg (M : DTM) (c : Cfg M.size) : Cfg M.size :=
  if c.state = M.accept ∨ c.state = M.reject then c
  else
    ⟨(M.step c.state (c.tape c.head)).1,
      writeTape c.tape c.head (M.step c.state (c.tape c.head)).2.1,
      (M.step c.state (c.tape c.head)).2.2.apply c.head⟩

/-- The initial configuration of `M` on input `x`. -/
def DTM.init (M : DTM) (x : Word) : Cfg M.size := ⟨M.start, initTape x, 0⟩

/-- The configuration of `M` on input `x` after `k` steps. -/
def DTM.run (M : DTM) (x : Word) (k : ℕ) : Cfg M.size :=
  M.stepCfg^[k] (M.init x)

/-- `M` decides the language `L` within time `T` if, on every input `x`, after
`T |x|` steps the machine has halted, and it is in the accepting state exactly
when `x ∈ L`. -/
def DTM.DecidesInTime (M : DTM) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x : Word,
    M.Halted (M.run x (T x.length)) ∧
      ((M.run x (T x.length)).state = M.accept ↔ x ∈ L)

/-! ## Polynomial bounds -/

/-- A time bound `T : ℕ → ℕ` is polynomial if `T n ≤ c * (n+1)^k` for some
constants `c` and `k`. -/
def IsPolyBound (T : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, T n ≤ c * (n + 1) ^ k

/-! ## The class P -/

/-- `P` is the class of languages decided by a deterministic Turing machine in
polynomial time. -/
def P : Set Language :=
  {L | ∃ M : DTM, ∃ T : ℕ → ℕ, IsPolyBound T ∧ M.DecidesInTime L T}

/-! ## Nondeterministic machines and the class NP -/

/-- A nondeterministic one-tape Turing machine: the transitions form a relation
`next` instead of a function. -/
structure NTM where
  /-- Number of control states. -/
  size : ℕ
  /-- The initial state. -/
  start : Fin size
  /-- The accepting state. -/
  accept : Fin size
  /-- Transition relation: from a state and the scanned symbol, any of the
  related triples (new state, symbol written, head movement) may be chosen. -/
  next : Fin size → Sym → Fin size × Sym × Move → Prop

/-- One nondeterministic step, as a relation between configurations. -/
def NTM.StepRel (M : NTM) (c c' : Cfg M.size) : Prop :=
  ∃ q s m, M.next c.state (c.tape c.head) (q, s, m) ∧
    c' = ⟨q, writeTape c.tape c.head s, m.apply c.head⟩

/-- `M.ReachIn k c c'` says that `c'` is reachable from `c` in exactly `k`
nondeterministic steps. -/
def NTM.ReachIn (M : NTM) : ℕ → Cfg M.size → Cfg M.size → Prop
  | 0, c, c' => c = c'
  | k + 1, c, c' => ∃ d, M.StepRel c d ∧ M.ReachIn k d c'

/-- `M` accepts `x` within `t` steps if some computation path of length at most
`t` starting from the initial configuration reaches the accepting state. -/
def NTM.AcceptsWithin (M : NTM) (x : Word) (t : ℕ) : Prop :=
  ∃ k ≤ t, ∃ c : Cfg M.size,
    M.ReachIn k ⟨M.start, initTape x, 0⟩ c ∧ c.state = M.accept

/-- `NP` is the class of languages accepted by a nondeterministic Turing
machine in polynomial time. -/
def NP : Set Language :=
  {L | ∃ M : NTM, ∃ T : ℕ → ℕ, IsPolyBound T ∧
    ∀ x : Word, x ∈ L ↔ M.AcceptsWithin x (T x.length)}

/-! ## Polynomial-time reducibility -/

/-- A function on words is polynomial-time computable if some deterministic
machine, run for polynomially many steps, halts in its accepting state with the
value of the function written on the tape (in the same format as an input). -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  ∃ M : DTM, ∃ T : ℕ → ℕ, IsPolyBound T ∧ ∀ x : Word,
    (M.run x (T x.length)).state = M.accept ∧
      (M.run x (T x.length)).tape = initTape (f x)

/-- Polynomial-time many-one reducibility: `A ≤p B` if there is a
polynomial-time computable `f` with `x ∈ A ↔ f x ∈ B`. -/
def PolyReducible (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTimeComputable f ∧ ∀ x : Word, x ∈ A ↔ f x ∈ B

@[inherit_doc] infix:50 " ≤p " => PolyReducible

/-- A language is NP-hard if every language in `NP` reduces to it in
polynomial time. -/
def NPHard (L : Language) : Prop := ∀ A ∈ NP, A ≤p L

/-- A language is NP-complete if it lies in `NP` and is NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-! ## The statement -/

/-- **The P versus NP problem.** The statement that the class of languages
decidable in deterministic polynomial time differs from the class of languages
accepted in nondeterministic polynomial time. -/
def P_vs_NP_statement : Prop := P ≠ NP

/-! ## Basic sanity results -/

theorem writeTape_self (t : ℤ → Sym) (i : ℤ) : writeTape t i (t i) = t := by
  funext j
  by_cases hj : j = i <;> simp [writeTape, hj]

theorem stepCfg_of_halted {M : DTM} {c : Cfg M.size} (h : M.Halted c) :
    M.stepCfg c = c := by
  unfold DTM.stepCfg
  exact if_pos h

theorem run_accept_add {M : DTM} {x : Word} {k : ℕ}
    (h : (M.run x k).state = M.accept) : ∀ d, (M.run x (k + d)).state = M.accept := by
  intro d
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have hstep : M.run x (k + (d + 1)) = M.stepCfg (M.run x (k + d)) := by
        rw [show k + (d + 1) = (k + d) + 1 by ring]
        simp [DTM.run, Function.iterate_succ_apply']
      rw [hstep, stepCfg_of_halted (Or.inl ih)]
      exact ih

theorem run_accept_mono {M : DTM} {x : Word} {k : ℕ}
    (h : (M.run x k).state = M.accept) : ∀ j, k ≤ j → (M.run x j).state = M.accept := by
  intro j hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact run_accept_add h d

/-- The deterministic machine `M` viewed as a nondeterministic one. -/
def DTM.toNTM (M : DTM) : NTM where
  size := M.size
  start := M.start
  accept := M.accept
  next := fun q s r =>
    if q = M.accept ∨ q = M.reject then r = (q, s, Move.stay) else r = M.step q s

theorem toNTM_stepRel_iff (M : DTM) (c c' : Cfg M.size) :
    M.toNTM.StepRel c c' ↔ c' = M.stepCfg c := by
  constructor
  · rintro ⟨q, s, m, hn, rfl⟩
    by_cases h : c.state = M.accept ∨ c.state = M.reject
    · simp only [DTM.toNTM, if_pos h] at hn
      obtain ⟨rfl, rfl, rfl⟩ : q = c.state ∧ s = c.tape c.head ∧ m = Move.stay := by
        simpa [Prod.ext_iff] using hn
      rw [stepCfg_of_halted h, writeTape_self]
      rfl
    · simp only [DTM.toNTM, if_neg h] at hn
      simp only [DTM.stepCfg, if_neg h, ← hn]
  · rintro rfl
    by_cases h : c.state = M.accept ∨ c.state = M.reject
    · refine ⟨c.state, c.tape c.head, Move.stay, ?_, ?_⟩
      · simp only [DTM.toNTM, if_pos h]
      · rw [stepCfg_of_halted h, writeTape_self]
        rfl
    · refine ⟨(M.step c.state (c.tape c.head)).1, (M.step c.state (c.tape c.head)).2.1,
        (M.step c.state (c.tape c.head)).2.2, ?_, ?_⟩
      · simp only [DTM.toNTM, if_neg h]
      · simp only [DTM.stepCfg, if_neg h]

theorem toNTM_reachIn_iff (M : DTM) (k : ℕ) (c c' : Cfg M.size) :
    M.toNTM.ReachIn k c c' ↔ c' = M.stepCfg^[k] c := by
  induction k generalizing c with
  | zero => simp [NTM.ReachIn, eq_comm]
  | succ k ih =>
      simp only [NTM.ReachIn, Function.iterate_succ_apply]
      constructor
      · rintro ⟨d, hd, hr⟩
        rw [toNTM_stepRel_iff] at hd
        subst hd
        exact (ih _).1 hr
      · intro h
        exact ⟨M.stepCfg c, (toNTM_stepRel_iff M c _).2 rfl, (ih _).2 h⟩

/-- Every language decidable in deterministic polynomial time is accepted in
nondeterministic polynomial time. -/
theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨M, T, hT, hM⟩
  refine ⟨M.toNTM, T, hT, fun x => ?_⟩
  constructor
  · intro hx
    refine ⟨T x.length, le_rfl, M.run x (T x.length), ?_, ((hM x).2).2 hx⟩
    exact (toNTM_reachIn_iff M _ _ _).2 rfl
  · rintro ⟨k, hk, c, hc, hacc⟩
    rw [toNTM_reachIn_iff] at hc
    have hrun : M.run x k = c := by
      simpa [DTM.run, DTM.init, DTM.toNTM] using hc.symm
    have : (M.run x k).state = M.accept := by rw [hrun]; exact hacc
    exact ((hM x).2).1 (run_accept_mono this _ hk)

/-- The P versus NP problem, restated: some language accepted in
nondeterministic polynomial time is not decidable in deterministic polynomial
time. -/
theorem P_vs_NP_statement_iff : P_vs_NP_statement ↔ ∃ L, L ∈ NP ∧ L ∉ P := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (Set.Subset.antisymm P_subset_NP fun L hL => hc L hL)
  · rintro ⟨L, hNP, hP⟩ h
    exact hP (h ▸ hNP)

/-- Equivalently: `P ≠ NP` iff `NP` is not contained in `P`. -/
theorem P_vs_NP_statement_iff_not_subset : P_vs_NP_statement ↔ ¬ NP ⊆ P := by
  rw [P_vs_NP_statement_iff]
  constructor
  · rintro ⟨L, hNP, hP⟩ hsub
    exact hP (hsub hNP)
  · intro h
    by_contra hc
    exact h fun L hL => by
      by_contra hLP
      exact hc ⟨L, hL, hLP⟩

/-! ### The classes are nonempty -/

/-- A machine with two states which halts immediately; `b = true` means it
starts in (and stays in) the accepting state. -/
def trivialDTM (b : Bool) : DTM where
  size := 2
  start := if b then 0 else 1
  accept := 0
  reject := 1
  step := fun q s => (q, s, Move.stay)
  accept_ne_reject := by decide

theorem trivialDTM_run_zero (b : Bool) (x : Word) :
    ((trivialDTM b).run x 0).state = (trivialDTM b).start := rfl

theorem zero_isPolyBound : IsPolyBound (fun _ => 0) := ⟨0, 0, by simp⟩

/-- The empty language is decidable in polynomial time. -/
theorem empty_mem_P : (∅ : Language) ∈ P := by
  refine ⟨trivialDTM false, fun _ => 0, zero_isPolyBound, fun x => ?_⟩
  refine ⟨Or.inr rfl, ?_⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  show ¬ ((1 : Fin 2) = 0)
  decide

/-- The language of all words is decidable in polynomial time. -/
theorem univ_mem_P : (Set.univ : Language) ∈ P := by
  refine ⟨trivialDTM true, fun _ => 0, zero_isPolyBound, fun x => ?_⟩
  exact ⟨Or.inl rfl, iff_of_true rfl (Set.mem_univ x)⟩

/-- Both trivial languages are in `NP` as well. -/
theorem empty_mem_NP : (∅ : Language) ∈ NP := P_subset_NP empty_mem_P

theorem univ_mem_NP : (Set.univ : Language) ∈ NP := P_subset_NP univ_mem_P

/-! ### `P` is closed under complementation -/

/-- The machine `M` with its accepting and rejecting states exchanged. -/
def DTM.swap (M : DTM) : DTM where
  size := M.size
  start := M.start
  accept := M.reject
  reject := M.accept
  step := M.step
  accept_ne_reject := M.accept_ne_reject.symm

theorem swap_stepCfg (M : DTM) (c : Cfg M.size) : M.swap.stepCfg c = M.stepCfg c := by
  by_cases h : c.state = M.accept ∨ c.state = M.reject
  · rw [stepCfg_of_halted (M := M.swap) (Or.symm h), stepCfg_of_halted h]
  · have h' : ¬ (c.state = M.reject ∨ c.state = M.accept) := fun hc => h (Or.symm hc)
    simp only [DTM.stepCfg, DTM.swap, if_neg h, if_neg h']

theorem swap_run (M : DTM) (x : Word) (k : ℕ) : M.swap.run x k = M.run x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : M.swap.run x (k + 1) = M.swap.stepCfg (M.swap.run x k) := by
        simp [DTM.run, Function.iterate_succ_apply']
      have h2 : M.run x (k + 1) = M.stepCfg (M.run x k) := by
        simp [DTM.run, Function.iterate_succ_apply']
      rw [h1, h2, ih, swap_stepCfg]

/-- The class `P` is closed under complementation. -/
theorem compl_mem_P {L : Language} (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨M, T, hT, hM⟩ := h
  refine ⟨M.swap, T, hT, fun x => ?_⟩
  obtain ⟨hhalt, hiff⟩ := hM x
  rw [swap_run]
  refine ⟨Or.symm hhalt, ?_⟩
  show (M.run x (T x.length)).state = M.reject ↔ x ∈ Lᶜ
  simp only [Set.mem_compl_iff]
  constructor
  · intro hst hx
    exact M.accept_ne_reject ((hiff.2 hx).symm.trans hst)
  · intro hx
    rcases hhalt with ha | hr
    · exact absurd (hiff.1 ha) hx
    · exact hr

/-! ### Polynomial-time reducibility is reflexive -/

/-- The identity function is polynomial-time computable. -/
theorem polyTimeComputable_id : PolyTimeComputable (fun x => x) := by
  refine ⟨trivialDTM true, fun _ => 0, zero_isPolyBound, fun x => ⟨rfl, rfl⟩⟩

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

