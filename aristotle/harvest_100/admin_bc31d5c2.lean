/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-! ## Tape alphabet, configurations and machines -/

/-- The tape alphabet: `none` is the blank symbol, `some b` a bit. -/
abbrev Alpha := Option Bool

/-- A language: a set of finite bit strings, presented as a predicate. -/
abbrev Language := List Bool → Prop

/-- A configuration of a one-tape Turing machine with state space `Λ`:
the current state, the (two-way infinite) tape contents and the head position. -/
structure Cfg (Λ : Type) where
  state : Λ
  tape : Int → Alpha
  pos : Int

/-- A (in general nondeterministic) one-tape Turing machine with state space `Λ`.
`δ q a (q', a', d)` holds when, reading the symbol `a` in state `q`, the machine may move
to state `q'`, write `a'` and move right (`d = true`) or left (`d = false`).
A state/symbol pair with no transition is a halting situation. -/
structure NTM (Λ : Type) where
  /-- the initial state -/
  start : Λ
  /-- the accepting states -/
  accept : Λ → Prop
  /-- the transition relation -/
  δ : Λ → Alpha → (Λ × Alpha × Bool) → Prop

variable {Λ : Type}

/-- The machine is deterministic: at most one transition per (state, symbol) pair. -/
def NTM.Deterministic (M : NTM Λ) : Prop :=
  ∀ q a y y', M.δ q a y → M.δ q a y' → y = y'

/-- Writing the symbol `a` in cell `p` of the tape `t`. -/
def writeTape (t : Int → Alpha) (p : Int) (a : Alpha) : Int → Alpha :=
  fun i => if i = p then a else t i

/-- One computation step of `M`. -/
def Step (M : NTM Λ) (c c' : Cfg Λ) : Prop :=
  ∃ q a d, M.δ c.state (c.tape c.pos) (q, a, d) ∧
    c' = ⟨q, writeTape c.tape c.pos a, c.pos + (if d then 1 else -1)⟩

/-- `c` is a halting configuration: no transition applies. -/
def Halted (M : NTM Λ) (c : Cfg Λ) : Prop :=
  ¬ ∃ y, M.δ c.state (c.tape c.pos) y

/-- `StepN M n c c'` : the configuration `c'` is reachable from `c` in exactly `n` steps. -/
def StepN (M : NTM Λ) : Nat → Cfg Λ → Cfg Λ → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c'', Step M c c'' ∧ StepN M n c'' c'

/-- The tape holding the input string `x` in cells `0, 1, …, |x| - 1`, blank elsewhere. -/
def inputTape (x : List Bool) : Int → Alpha :=
  fun i => if 0 ≤ i then x[i.toNat]? else none

/-- The initial configuration of `M` on input `x`. -/
def initCfg (M : NTM Λ) (x : List Bool) : Cfg Λ :=
  ⟨M.start, inputTape x, 0⟩

/-! ## Acceptance, decision, output -/

/-- `M` accepts `x` within `t` steps: some computation of length at most `t` reaches a
halting configuration whose state is accepting. -/
def AcceptsIn (M : NTM Λ) (x : List Bool) (t : Nat) : Prop :=
  ∃ k, k ≤ t ∧ ∃ c, StepN M k (initCfg M x) c ∧ Halted M c ∧ M.accept c.state

/-- `M` decides the language `L` within the time bound `T`: on every input `x` it reaches a
halting configuration within `T |x|` steps, and that configuration is accepting exactly when
`x ∈ L`. -/
def DecidesIn (M : NTM Λ) (L : Language) (T : Nat → Nat) : Prop :=
  ∀ x, ∃ k, k ≤ T x.length ∧ ∃ c, StepN M k (initCfg M x) c ∧ Halted M c ∧
    (M.accept c.state ↔ L x)

/-- The configuration `c` has output `y`: the tape holds `y` in the cells `0, …, |y| - 1`
and is blank in cell `|y|`. -/
def Outputs (c : Cfg Λ) (y : List Bool) : Prop :=
  (∀ i : Nat, i < y.length → c.tape (i : Int) = y[i]?) ∧ c.tape (y.length : Int) = none

/-- `M` computes the string function `f` within the time bound `T`. -/
def ComputesIn (M : NTM Λ) (f : List Bool → List Bool) (T : Nat → Nat) : Prop :=
  ∀ x, ∃ k, k ≤ T x.length ∧ ∃ c, StepN M k (initCfg M x) c ∧ Halted M c ∧ Outputs c (f x)

/-- `T` is bounded by a polynomial. -/
def IsPoly (T : Nat → Nat) : Prop :=
  ∃ c d : Nat, ∀ n, T n ≤ c * n ^ d + c

/-! ## The classes P and NP, and polynomial-time reducibility -/

/-- The class `P`: the languages decided by some deterministic Turing machine with finitely
many states within a polynomial time bound. -/
def P (L : Language) : Prop :=
  ∃ (n : Nat) (M : NTM (Fin (n + 1))) (T : Nat → Nat),
    M.Deterministic ∧ IsPoly T ∧ DecidesIn M L T

/-- The class `NP`: the languages accepted by some nondeterministic Turing machine with
finitely many states within a polynomial time bound. -/
def NP (L : Language) : Prop :=
  ∃ (n : Nat) (M : NTM (Fin (n + 1))) (T : Nat → Nat),
    IsPoly T ∧ ∀ x, L x ↔ AcceptsIn M x (T x.length)

/-- A string function is polynomial-time computable. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (n : Nat) (M : NTM (Fin (n + 1))) (T : Nat → Nat),
    M.Deterministic ∧ IsPoly T ∧ ComputesIn M f T

/-- Polynomial-time many-one reducibility, `L ≤ₚ L'`. -/
def PolyReducible (L L' : Language) : Prop :=
  ∃ f, PolyTimeComputable f ∧ ∀ x, L x ↔ L' (f x)

@[inherit_doc] infix:50 " ≤ₚ " => PolyReducible

/-- `L` is `NP`-hard for polynomial-time many-one reductions. -/
def NPHard (L : Language) : Prop := ∀ L', NP L' → L' ≤ₚ L

/-- `L` is `NP`-complete. -/
def NPComplete (L : Language) : Prop := NP L ∧ NPHard L

/-! ## Basic facts -/

/-- A deterministic machine has at most one successor configuration. -/
theorem step_det {M : NTM Λ} (hM : M.Deterministic) {c c₁ c₂ : Cfg Λ}
    (h₁ : Step M c c₁) (h₂ : Step M c c₂) : c₁ = c₂ := by
  obtain ⟨q, a, d, hd, rfl⟩ := h₁
  obtain ⟨q', a', d', hd', rfl⟩ := h₂
  have h := hM _ _ _ _ hd hd'
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem halted_not_step {M : NTM Λ} {c c' : Cfg Λ} (h : Halted M c) : ¬ Step M c c' := by
  intro hs
  obtain ⟨q, a, d, hd, -⟩ := hs
  exact h ⟨(q, a, d), hd⟩

/-- A deterministic machine reaches at most one halting configuration from a given
starting configuration. -/
theorem halted_unique {M : NTM Λ} (hM : M.Deterministic) :
    ∀ (k k' : Nat) (c₀ c c' : Cfg Λ), StepN M k c₀ c → Halted M c →
      StepN M k' c₀ c' → Halted M c' → c = c' := by
  intro k
  induction k with
  | zero =>
      intro k' c₀ c c' h hc h' hc'
      cases h
      cases k' with
      | zero => cases h'; rfl
      | succ j =>
          obtain ⟨c₁, hstep, -⟩ := h'
          exact absurd hstep (halted_not_step hc)
  | succ i ih =>
      intro k' c₀ c c' h hc h' hc'
      obtain ⟨c₁, hstep, hrest⟩ := h
      cases k' with
      | zero =>
          cases h'
          exact absurd hstep (halted_not_step hc')
      | succ j =>
          obtain ⟨c₂, hstep', hrest'⟩ := h'
          have hc₁ : c₁ = c₂ := step_det hM hstep hstep'
          subst hc₁
          exact ih j c₁ c c' hrest hc hrest' hc'

/-- Every language in `P` lies in `NP`: a deterministic machine is in particular a
nondeterministic one, and by uniqueness of its halting configuration it accepts exactly the
strings of the language it decides. -/
theorem P_subset_NP (L : Language) (hL : P L) : NP L := by
  obtain ⟨n, M, T, hdet, hpoly, hdec⟩ := hL
  refine ⟨n, M, T, hpoly, fun x => ?_⟩
  obtain ⟨k, hk, c, hrun, hhalt, hiff⟩ := hdec x
  constructor
  · intro hx
    exact ⟨k, hk, c, hrun, hhalt, hiff.mpr hx⟩
  · intro hacc
    obtain ⟨k', hk', c', hrun', hhalt', hacc'⟩ := hacc
    have hcc : c = c' := halted_unique hdet k k' _ c c' hrun hhalt hrun' hhalt'
    subst hcc
    exact hiff.mp hacc'

/-- The identity function is polynomial-time computable: the machine with no transitions at
all halts immediately, leaving the input on the tape. -/
theorem polyTimeComputable_id : PolyTimeComputable (fun x => x) := by
  refine ⟨0, ⟨0, fun _ => False, fun _ _ _ => False⟩, fun _ => 0, ?_, ⟨0, 0, ?_⟩, ?_⟩
  · intro q a y y' h _
    exact h.elim
  · intro n
    exact Nat.zero_le _
  · intro x
    refine ⟨0, Nat.le_refl 0, initCfg _ x, rfl, ?_, ?_, ?_⟩
    · intro hex
      exact hex.elim fun _ hy => hy
    · intro i hi
      show inputTape x (i : Int) = x[i]?
      unfold inputTape
      rw [if_pos (by omega)]
      have h : ((i : Int)).toNat = i := by omega
      rw [h]
    · show inputTape x (x.length : Int) = none
      unfold inputTape
      rw [if_pos (by omega)]
      have h : ((x.length : Int)).toNat = x.length := by omega
      rw [h]
      exact List.getElem?_eq_none (Nat.le_refl _)

/-- Polynomial-time many-one reducibility is reflexive. -/
theorem polyReducible_refl (L : Language) : L ≤ₚ L :=
  ⟨fun x => x, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- The trivially-halting machine with no transitions, whose accepting states are given by
`A`. It is deterministic and halts in its start state in `0` steps on every input. -/
def trivialTM (A : Prop) : NTM (Fin 1) := ⟨0, fun _ => A, fun _ _ _ => False⟩

theorem trivialTM_deterministic (A : Prop) : (trivialTM A).Deterministic := by
  intro q a y y' h _
  exact h.elim

theorem trivialTM_halted (A : Prop) (c : Cfg (Fin 1)) : Halted (trivialTM A) c := by
  intro hex
  exact hex.elim fun _ hy => hy

/-- Sanity check: the empty language is in `P` (hence, by `P_subset_NP`, in `NP`). -/
theorem P_empty : P (fun _ => False) := by
  refine ⟨0, trivialTM False, fun _ => 0, trivialTM_deterministic _, ⟨0, 0, fun n => Nat.zero_le _⟩,
    fun x => ⟨0, Nat.le_refl 0, initCfg _ x, rfl, trivialTM_halted _ _, Iff.rfl⟩⟩

/-- Sanity check: the language of all bit strings is in `P`. -/
theorem P_univ : P (fun _ => True) := by
  refine ⟨0, trivialTM True, fun _ => 0, trivialTM_deterministic _, ⟨0, 0, fun n => Nat.zero_le _⟩,
    fun x => ⟨0, Nat.le_refl 0, initCfg _ x, rfl, trivialTM_halted _ _, Iff.rfl⟩⟩

/-! ## The statement -/

/-- The assertion `P ≠ NP` for the two classes defined above. -/
def P_ne_NP : Prop := P ≠ NP

/-- **The P versus NP statement.**

With `P` and `NP` defined via polynomial-time bounded deterministic, resp. nondeterministic,
one-tape Turing machines, the assertion `P ≠ NP` is equivalent to the existence of a language
that is accepted by some polynomial-time nondeterministic machine but decided by no
polynomial-time deterministic machine.

This equivalent (contrapositive) reformulation of the statement is what is proved here; the
assertion `P ≠ NP` itself is an open problem. The nontrivial direction uses `P ⊆ NP`. -/
theorem P_vs_NP_statement :
    P_ne_NP ↔ ∃ L : Language, NP L ∧ ¬ P L := by
  constructor
  · intro h
    refine Classical.byContradiction fun hcon => h ?_
    funext L
    refine propext ⟨fun hLP => P_subset_NP L hLP, fun hLNP => ?_⟩
    exact Classical.byContradiction fun hnp => hcon ⟨L, hLNP, hnp⟩
  · intro hex heq
    obtain ⟨L, hNP, hP⟩ := hex
    exact hP (by rw [heq]; exact hNP)

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

