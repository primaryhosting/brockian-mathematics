/-
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file gives a self-contained formalization of the classes `P` and `NP` of languages
over the binary alphabet, in terms of time-bounded (deterministic and nondeterministic)
Turing machines, together with polynomial-time many-one reducibility, NP-hardness and
NP-completeness.

The target theorem `Frontier.P_vs_NP_statement` records the precise statement of the
P vs NP problem together with the facts about it that are provable outright:

* `P ⊆ NP`;
* `P ≠ NP` is equivalent to the existence of a language in `NP` which is not in `P`;
* if some NP-complete language fails to be in `P`, then `P ≠ NP`.

(The truth value of `P ≠ NP` itself is of course not settled here.)
-/

namespace Frontier

/-- Tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym : Type := Option Bool

/-- A word is a finite binary string. -/
abbrev Word : Type := List Bool

/-- A language is a set of binary strings. -/
abbrev Language : Type := Set Word

/-- A tape is a bi-infinite sequence of symbols. -/
abbrev Tape : Type := ℤ → Sym

/-- The initial tape holding the input `x` in cells `0, 1, …, |x| - 1`, blank elsewhere. -/
def inputTape (x : Word) : Tape := fun i => if 0 ≤ i then x[i.toNat]? else none

/-- A configuration: the current state, the head position, and the tape contents. -/
abbrev Conf (Q : Type) : Type := Q × ℤ × Tape

/-- `Poly T` says that `T : ℕ → ℕ` is bounded by a polynomial. -/
def Poly (T : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, T n ≤ c * n ^ k + c

/-! ## Deterministic machines -/

/-- A deterministic one-tape Turing machine over the alphabet `Sym` with a finite state set.
`next q a` gives the new state, the symbol written, and the direction of the head move
(`true` = right, `false` = left).  A state `q` with `out q = some b` is a final state where
the machine has halted with answer `b`; the machine moves exactly in non-final states. -/
structure DTM where
  /-- The (finite) set of states. -/
  Q : Type
  /-- Finiteness of the state set. -/
  qFintype : Fintype Q
  /-- The initial state. -/
  start : Q
  /-- The transition function. -/
  next : Q → Sym → Q × Sym × Bool
  /-- `out q = some b` marks `q` as a halting state with answer `b`. -/
  out : Q → Option Bool

attribute [instance] DTM.qFintype

namespace DTM

variable (M : DTM)

/-- A configuration is halted when its state is a final state. -/
def Halted (c : Conf M.Q) : Prop := (M.out c.1).isSome

/-- One step of computation; halted configurations are fixed points. -/
def stepc (c : Conf M.Q) : Conf M.Q :=
  if (M.out c.1).isSome then c
  else
    ((M.next c.1 (c.2.2 c.2.1)).1,
      c.2.1 + (if (M.next c.1 (c.2.2 c.2.1)).2.2 then 1 else -1),
      Function.update c.2.2 c.2.1 (M.next c.1 (c.2.2 c.2.1)).2.1)

/-- The configuration reached after `n` steps. -/
def run : Conf M.Q → ℕ → Conf M.Q
  | c, 0 => c
  | c, (n + 1) => run (M.stepc c) n

/-- The initial configuration on input `x`. -/
def init (x : Word) : Conf M.Q := (M.start, 0, inputTape x)

/-- `M.Decides L T` : on every input `x` the machine halts within `T |x|` steps, with
answer `true` exactly when `x ∈ L`. -/
def Decides (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x : Word, ∃ t ≤ T x.length, ∃ b : Bool,
    M.out (M.run (M.init x) t).1 = some b ∧ (b = true ↔ x ∈ L)

/-- `M.Computes f T` : on every input `x` the machine halts within `T |x|` steps with the
tape holding the word `f x`. -/
def Computes (f : Word → Word) (T : ℕ → ℕ) : Prop :=
  ∀ x : Word, ∃ t ≤ T x.length,
    (M.out (M.run (M.init x) t).1).isSome ∧ (M.run (M.init x) t).2.2 = inputTape (f x)

end DTM

/-- The class `P`: languages decidable by a deterministic Turing machine in polynomial time. -/
def P : Set Language := {L | ∃ (M : DTM) (T : ℕ → ℕ), Poly T ∧ M.Decides L T}

/-! ## Nondeterministic machines -/

/-- A nondeterministic one-tape Turing machine with a finite state set: `next q a` is the set
of possible moves, and `accept` is the set of accepting states. -/
structure NTM where
  /-- The (finite) set of states. -/
  Q : Type
  /-- Finiteness of the state set. -/
  qFintype : Fintype Q
  /-- The initial state. -/
  start : Q
  /-- The transition relation, given as a set of possible moves. -/
  next : Q → Sym → Set (Q × Sym × Bool)
  /-- The set of accepting states. -/
  accept : Set Q

attribute [instance] NTM.qFintype

namespace NTM

variable (M : NTM)

/-- One nondeterministic step. -/
def stepRel (c c' : Conf M.Q) : Prop :=
  ∃ p ∈ M.next c.1 (c.2.2 c.2.1),
    c' = (p.1, c.2.1 + (if p.2.2 then 1 else -1), Function.update c.2.2 c.2.1 p.2.1)

/-- `M.reach n c c'` : the configuration `c'` is reachable from `c` in exactly `n` steps. -/
def reach : ℕ → Conf M.Q → Conf M.Q → Prop
  | 0, c, c' => c' = c
  | (n + 1), c, c' => ∃ c'', M.stepRel c c'' ∧ reach n c'' c'

/-- `M.Accepts x T` : some computation path of length at most `T` on input `x` reaches an
accepting state. -/
def Accepts (x : Word) (T : ℕ) : Prop :=
  ∃ t ≤ T, ∃ c, M.reach t (M.start, 0, inputTape x) c ∧ c.1 ∈ M.accept

end NTM

/-- The class `NP`: languages accepted by a nondeterministic Turing machine in polynomial
time. -/
def NP : Set Language :=
  {L | ∃ (M : NTM) (T : ℕ → ℕ), Poly T ∧ ∀ x, x ∈ L ↔ M.Accepts x (T x.length)}

/-! ## Polynomial-time reducibility -/

/-- `PolyReducible L L'` : `L` is polynomial-time many-one reducible to `L'`. -/
def PolyReducible (L L' : Language) : Prop :=
  ∃ (f : Word → Word) (M : DTM) (T : ℕ → ℕ),
    Poly T ∧ M.Computes f T ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] infix:50 " ≤p " => PolyReducible

/-- A language is NP-hard if every language in `NP` reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤p L

/-- A language is NP-complete if it lies in `NP` and is NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-! ## Basic facts -/

namespace DTM

variable {M : DTM}

theorem run_succ (c : Conf M.Q) (n : ℕ) : M.run c (n + 1) = M.stepc (M.run c n) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simpa [run] using ih (M.stepc c)

theorem run_of_halted {c : Conf M.Q} {t : ℕ} (h : (M.out (M.run c t).1).isSome) (s : ℕ) :
    M.run c (t + s) = M.run c t := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have : M.run c (t + s + 1) = M.stepc (M.run c (t + s)) := run_succ c (t + s)
      rw [show t + (s + 1) = t + s + 1 from rfl, this, ih]
      simp [stepc, h]

theorem out_unique {c : Conf M.Q} {t₁ t₂ : ℕ} {b₁ b₂ : Bool}
    (h₁ : M.out (M.run c t₁).1 = some b₁) (h₂ : M.out (M.run c t₂).1 = some b₂) :
    b₁ = b₂ := by
  have e₁ : M.run c (t₁ + (max t₁ t₂ - t₁)) = M.run c t₁ :=
    run_of_halted (by rw [h₁]; simp) _
  have e₂ : M.run c (t₂ + (max t₁ t₂ - t₂)) = M.run c t₂ :=
    run_of_halted (by rw [h₂]; simp) _
  rw [show t₁ + (max t₁ t₂ - t₁) = max t₁ t₂ by omega] at e₁
  rw [show t₂ + (max t₁ t₂ - t₂) = max t₁ t₂ by omega] at e₂
  have : some b₁ = some b₂ := by rw [← h₁, ← h₂, ← e₁, ← e₂]
  simpa using this

end DTM

/-- The nondeterministic machine simulating a deterministic one. -/
def DTM.toNTM (M : DTM) : NTM where
  Q := M.Q
  qFintype := M.qFintype
  start := M.start
  next := fun q a => if (M.out q).isSome then ∅ else {M.next q a}
  accept := {q | M.out q = some true}

namespace DTM

variable {M : DTM}

theorem toNTM_stepRel_iff {c c' : Conf M.Q} :
    M.toNTM.stepRel c c' ↔ ¬ (M.out c.1).isSome ∧ c' = M.stepc c := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [DTM.toNTM] at hp ⊢
    by_cases h : (M.out c.1).isSome
    · simp [h] at hp
    · simp [h] at hp
      subst hp
      exact ⟨h, by simp [stepc, h]⟩
  · rintro ⟨h, rfl⟩
    refine ⟨M.next c.1 (c.2.2 c.2.1), ?_, ?_⟩
    · simp [DTM.toNTM, h]
    · simp [stepc, h]

theorem reach_snoc {n : ℕ} {c c' c'' : Conf M.Q}
    (h : M.toNTM.reach n c c') (hs : M.toNTM.stepRel c' c'') : M.toNTM.reach (n + 1) c c'' := by
  induction n generalizing c with
  | zero =>
      refine ⟨c'', ?_, rfl⟩
      simp only [NTM.reach] at h
      subst h
      exact hs
  | succ n ih =>
      obtain ⟨d, hd, hrest⟩ := h
      exact ⟨d, hd, ih hrest⟩

theorem exists_reach_run (c : Conf M.Q) (t : ℕ) : ∃ s ≤ t, M.toNTM.reach s c (M.run c t) := by
  induction t with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ t ih =>
      obtain ⟨s, hs, hr⟩ := ih
      by_cases h : (M.out (M.run c t).1).isSome
      · refine ⟨s, by omega, ?_⟩
        rw [run_succ, stepc, if_pos h]
        exact hr
      · refine ⟨s + 1, by omega, ?_⟩
        rw [run_succ]
        exact reach_snoc hr (toNTM_stepRel_iff.mpr ⟨h, rfl⟩)

theorem reach_eq_run {t : ℕ} {c c' : Conf M.Q} (h : M.toNTM.reach t c c') : c' = M.run c t := by
  induction t generalizing c with
  | zero => simpa [run] using h
  | succ t ih =>
      obtain ⟨d, hd, hrest⟩ := h
      obtain ⟨-, rfl⟩ := toNTM_stepRel_iff.mp hd
      simpa [run] using ih hrest

end DTM

/-- Every polynomial-time decidable language is accepted by a polynomial-time
nondeterministic machine. -/
theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨M, T, hT, hdec⟩
  refine ⟨M.toNTM, T, hT, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨t, ht, b, hb, hbL⟩ := hdec x
    have hb' : b = true := hbL.mpr hx
    subst hb'
    obtain ⟨s, hs, hr⟩ := DTM.exists_reach_run (M.init x) t
    exact ⟨s, le_trans hs ht, _, hr, hb⟩
  · rintro ⟨t, ht, c, hr, hacc⟩
    have hc : c = M.run (M.init x) t := DTM.reach_eq_run hr
    subst hc
    obtain ⟨t₀, ht₀, b, hb, hbL⟩ := hdec x
    have : true = b := DTM.out_unique hacc hb
    exact hbL.mp this.symm

/-- The machine that halts immediately, accepting its input unchanged. -/
def idDTM : DTM where
  Q := Unit
  qFintype := inferInstance
  start := ()
  next := fun _ _ => ((), none, true)
  out := fun _ => some true

theorem polyReducible_refl (L : Language) : L ≤p L := by
  refine ⟨id, idDTM, fun _ => 0, ⟨0, 0, by simp⟩, fun x => ⟨0, le_rfl, ?_, rfl⟩, fun _ => Iff.rfl⟩
  simp [idDTM, DTM.run, DTM.init]

/-- The machine that halts immediately, rejecting its input. -/
def rejectDTM : DTM where
  Q := Unit
  qFintype := inferInstance
  start := ()
  next := fun _ _ => ((), none, true)
  out := fun _ => some false

/-- Sanity check: the classes are not vacuous, e.g. the empty language is in `P`. -/
theorem empty_mem_P : (∅ : Language) ∈ P :=
  ⟨rejectDTM, fun _ => 0, ⟨0, 0, by simp⟩,
    fun x => ⟨0, le_rfl, false, by simp [rejectDTM, DTM.run, DTM.init], by simp⟩⟩

/-- Sanity check: the whole space of words is in `P`. -/
theorem univ_mem_P : (Set.univ : Language) ∈ P :=
  ⟨idDTM, fun _ => 0, ⟨0, 0, by simp⟩,
    fun x => ⟨0, le_rfl, true, by simp [idDTM, DTM.run, DTM.init], by simp⟩⟩

theorem empty_mem_NP : (∅ : Language) ∈ NP := P_subset_NP empty_mem_P

/-! ## The statement of the P vs NP problem -/

/-- **The P vs NP problem.**

With `P` and `NP` defined via time-bounded deterministic resp. nondeterministic Turing
machines, and `≤p` polynomial-time many-one reducibility, we record:

1. `P ⊆ NP`;
2. `P ≠ NP` holds if and only if there is a language in `NP` that is not in `P`
   (the contrapositive/equivalent form of the conjecture);
3. exhibiting an NP-complete language outside `P` suffices to separate the classes. -/
theorem P_vs_NP_statement :
    P ⊆ NP ∧
      ((P ≠ NP) ↔ ∃ L : Language, L ∈ NP ∧ L ∉ P) ∧
      (∀ L : Language, NPComplete L → L ∉ P → P ≠ NP) := by
  refine ⟨P_subset_NP, ⟨?_, ?_⟩, ?_⟩
  · intro hne
    by_contra hall
    push_neg at hall
    exact hne (le_antisymm P_subset_NP fun L hL => hall L hL)
  · rintro ⟨L, hLNP, hLP⟩ hEq
    exact hLP (hEq ▸ hLNP)
  · rintro L ⟨hLNP, -⟩ hLP hEq
    exact hLP (hEq ▸ hLNP)

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

