import RequestProject.Frontier.Basic
import RequestProject.Frontier.Tableau
import RequestProject.Frontier.Correctness
import RequestProject.Frontier.Size
import RequestProject.Frontier.NP

import Mathlib

/-!
# The Cook–Levin theorem (tableau reduction)

This file develops, from scratch, the core of the Cook–Levin theorem: the *tableau
reduction* from an arbitrary nondeterministic Turing machine computation to the
satisfiability of a CNF formula.

## Main results

* `Frontier.tableau_satisfiable_iff`: for a well-formed nondeterministic Turing machine
  `M` with a tape of `N` cells, a time bound `T` and an input tape `x`, the explicitly
  constructed CNF formula `Frontier.tableau M N T x` is satisfiable if and only if `M`
  has an accepting computation on `x` of length `T`.
* `Frontier.tableau_length_le`: the tableau has polynomially many clauses.
* `Frontier.cook_levin`: **SAT is NP-hard**.  Every language in `Frontier.InNP` (defined
  via nondeterministic Turing machines with a polynomially bounded running time) is
  many-one reducible to satisfiability of CNF formulas, by the explicit reduction
  `Frontier.satReduction`, whose output has polynomially bounded size.
* `Frontier.satisfiable_iff_exists_certificate`: the membership half, at the level of
  certificates — a formula is satisfiable exactly when it admits a certificate of
  length `maxVar φ + 1` accepted by the explicit checker `Frontier.checkSat`.

## Scope

The hardness half is proved in full, including the polynomial bound on the size of the
produced formula; the reduction itself is an explicit, executable function.  What is
*not* formalised here is a machine-level cost model for computing the reduction, nor a
Turing machine implementation of a SAT verifier; the membership half is formalised in
the certificate form described above rather than by exhibiting such a machine.
-/

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

import RequestProject.Frontier.Size

/-!
# SAT is NP-hard

Polynomially bounded functions, the class NP defined via nondeterministic Turing
machines, the Cook-Levin reduction, and the certificate characterisation of
satisfiability.
-/

namespace Frontier

/-! ## SAT is NP-hard

We now package the tableau reduction as the statement that SAT is NP-hard.
A language over the binary alphabet is in NP when it is decided by a
nondeterministic Turing machine within a polynomially bounded number of steps. -/

/-- `f` is bounded by a polynomial. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d

theorem PolyBounded.const (k : ℕ) : PolyBounded (fun _ => k) := ⟨k, 0, by simp⟩

theorem PolyBounded.id : PolyBounded (fun n => n) := ⟨1, 1, by simp⟩

theorem PolyBounded.mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolyBounded g) :
    PolyBounded f := by
  obtain ⟨c, d, hcd⟩ := hg
  exact ⟨c, d, fun n => le_trans (h n) (hcd n)⟩

theorem PolyBounded.add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n + g n) := by
  obtain ⟨c₁, d₁, h₁⟩ := hf
  obtain ⟨c₂, d₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max d₁ d₂, fun n => ?_⟩
  have e₁ : (n + 1) ^ d₁ ≤ (n + 1) ^ max d₁ d₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (n + 1) ^ d₂ ≤ (n + 1) ^ max d₁ d₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f n + g n ≤ c₁ * (n + 1) ^ d₁ + c₂ * (n + 1) ^ d₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n + 1) ^ max d₁ d₂ + c₂ * (n + 1) ^ max d₁ d₂ :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (c₁ + c₂) * (n + 1) ^ max d₁ d₂ := by ring

theorem PolyBounded.mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n * g n) := by
  obtain ⟨c₁, d₁, h₁⟩ := hf
  obtain ⟨c₂, d₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, d₁ + d₂, fun n => ?_⟩
  calc f n * g n ≤ (c₁ * (n + 1) ^ d₁) * (c₂ * (n + 1) ^ d₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = (c₁ * c₂) * (n + 1) ^ (d₁ + d₂) := by rw [pow_add]; ring

theorem PolyBounded.pow {f : ℕ → ℕ} (hf : PolyBounded f) (k : ℕ) :
    PolyBounded (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using PolyBounded.const 1
  | succ k ih =>
    have := ih.mul hf
    refine PolyBounded.mono (fun n => ?_) this
    rw [pow_succ]

/-- Encoding of a binary word as an initial tape: `0` is the blank symbol, and the
letters `false`/`true` are the symbols `1`/`2`. -/
def inputTape (w : List Bool) : ℕ → ℕ := fun i =>
  match w[i]? with
  | none => 0
  | some b => if b then 2 else 1

theorem inputTape_lt_three (w : List Bool) (i : ℕ) : inputTape w i < 3 := by
  unfold inputTape
  rcases h : w[i]? with _ | b
  · norm_num
  · cases b <;> norm_num

/-- A language over the binary alphabet. -/
def Lang := List Bool → Prop

/-- `L` is in NP: some well-formed nondeterministic Turing machine with at least the
three input symbols accepts exactly the words of `L`, within a polynomially bounded
number of steps (and hence in polynomially bounded space). -/
def InNP (L : Lang) : Prop :=
  ∃ (M : NTM) (p : ℕ → ℕ), M.WF ∧ 3 ≤ M.nSymbols ∧ PolyBounded p ∧
    ∀ w : List Bool,
      L w ↔ M.AcceptsIn (p w.length + w.length + 1) (p w.length) (inputTape w)

/-- The explicit reduction: a word `w` is mapped to the tableau formula of `M` on the
input tape of `w`, with time bound `p |w|` and tape length `p |w| + |w| + 1`. -/
def satReduction (M : NTM) (p : ℕ → ℕ) (w : List Bool) : CNF :=
  tableau M (p w.length + w.length + 1) (p w.length) (inputTape w)

/-- **Cook–Levin: SAT is NP-hard.**  Every language in NP reduces to satisfiability of
CNF formulas by an explicit reduction whose output has polynomially bounded size.
The witnessing reduction is `Frontier.satReduction`. -/
theorem cook_levin (L : Lang) (hL : InNP L) :
    ∃ f : List Bool → CNF,
      (∃ c d : ℕ, ∀ w : List Bool, (f w).length ≤ c * (w.length + 1) ^ d) ∧
        ∀ w : List Bool, L w ↔ Satisfiable (f w) := by
  obtain ⟨M, p, hM, h3, hp, hL⟩ := hL
  refine ⟨satReduction M p, ?_, ?_⟩
  · -- polynomial size bound
    have hbound : PolyBounded (fun n =>
        20 * ((p n + 1) * (p n + n + 1 + M.nStates + M.nSymbols + 1) ^ 3)) := by
      refine PolyBounded.mul (PolyBounded.const 20) ?_
      refine PolyBounded.mul (hp.add (PolyBounded.const 1)) ?_
      exact PolyBounded.pow
        ((((hp.add PolyBounded.id).add (PolyBounded.const 1)).add
          (PolyBounded.const M.nStates)).add (PolyBounded.const M.nSymbols) |>.add
            (PolyBounded.const 1)) 3
    obtain ⟨c, d, hcd⟩ := hbound
    exact ⟨c, d, fun w => le_trans (tableau_length_le _ _ _ _) (hcd w.length)⟩
  · intro w
    rw [hL w, satReduction,
      tableau_satisfiable_iff hM (by omega) (fun i => lt_of_lt_of_le (inputTape_lt_three w i) h3)]

/-! ## SAT has short, efficiently checkable certificates

This is the "membership" half of NP-completeness, stated at the level of certificates:
every satisfiable formula has a certificate whose length is bounded by the size of the
formula, and the certificate is checked by the explicit Boolean function `checkSat`,
which simply evaluates the formula. -/

/-- The largest variable index occurring in a formula (or `0` if there is none). -/
def maxVar (φ : CNF) : ℕ := (φ.flatMap fun c => c.map Lit.var).foldr max 0

theorem le_foldr_max {l : List ℕ} {v : ℕ} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem var_le_maxVar {φ : CNF} {c : Clause} {l : Lit} (hc : c ∈ φ) (hl : l ∈ c) :
    l.var ≤ maxVar φ :=
  le_foldr_max (List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨l, hl, rfl⟩⟩)

/-- Evaluation only depends on the variables occurring in the formula. -/
theorem cnfEval_congr {σ τ : ℕ → Bool} {φ : CNF}
    (h : ∀ v, v ≤ maxVar φ → σ v = τ v) : cnfEval σ φ = cnfEval τ φ := by
  have hcl : ∀ c ∈ φ, clauseEval σ c = clauseEval τ c := by
    intro c hc
    rw [Bool.eq_iff_iff]
    simp only [clauseEval, List.any_eq_true]
    constructor
    · rintro ⟨l, hl, hlv⟩
      exact ⟨l, hl, by rwa [litEval, ← h l.var (var_le_maxVar hc hl)]⟩
    · rintro ⟨l, hl, hlv⟩
      exact ⟨l, hl, by rwa [litEval, h l.var (var_le_maxVar hc hl)]⟩
  rw [Bool.eq_iff_iff]
  simp only [cnfEval, List.all_eq_true]
  constructor
  · intro hh c hc; rw [← hcl c hc]; exact hh c hc
  · intro hh c hc; rw [hcl c hc]; exact hh c hc

/-- The assignment described by a certificate word. -/
def assignOf (w : List Bool) : ℕ → Bool := fun v => w.getD v false

/-- The certificate checker for SAT: evaluate the formula under the certificate. -/
def checkSat (φ : CNF) (w : List Bool) : Bool := cnfEval (assignOf w) φ

/-- **SAT has short certificates.**  A formula is satisfiable if and only if it has a
certificate of length `maxVar φ + 1` accepted by the explicit checker `checkSat`. -/
theorem satisfiable_iff_exists_certificate (φ : CNF) :
    Satisfiable φ ↔ ∃ w : List Bool, w.length = maxVar φ + 1 ∧ checkSat φ w = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range (maxVar φ + 1)).map σ, by simp, ?_⟩
    have hval : ∀ v, v ≤ maxVar φ →
        assignOf ((List.range (maxVar φ + 1)).map σ) v = σ v := by
      intro v hv
      have hlen : v < ((List.range (maxVar φ + 1)).map σ).length := by simp; omega
      simp only [assignOf, List.getD_eq_getElem _ _ hlen]
      simp
    rw [checkSat, cnfEval_congr (σ := assignOf ((List.range (maxVar φ + 1)).map σ)) (τ := σ) hval]
    exact hσ
  · rintro ⟨w, -, hw⟩
    exact ⟨assignOf w, hw⟩

/-! ## Sanity checks

The notions above are not degenerate: satisfiability is a nontrivial predicate, and
there are languages in `InNP`. -/

/-- The CNF formula `x₀ ∧ ¬x₀` is not satisfiable. -/
theorem not_satisfiable_example : ¬ Satisfiable [[⟨0, true⟩], [⟨0, false⟩]] := by
  rintro ⟨σ, hσ⟩
  cases hv : σ 0 <;> simp [cnfEval, clauseEval, litEval, hv] at hσ

/-- The CNF formula `x₀` is satisfiable. -/
theorem satisfiable_example : Satisfiable [[⟨0, true⟩]] :=
  ⟨fun _ => true, by simp [cnfEval, clauseEval, litEval]⟩

/-- A machine that immediately accepts and never moves. -/
def trivialNTM : NTM where
  nStates := 1
  nSymbols := 3
  start := 0
  accept := 0
  δ := fun _ _ _ => (0, 0, Dir.S)

theorem trivialNTM_wf : trivialNTM.WF :=
  ⟨by norm_num [trivialNTM], by norm_num [trivialNTM], by intro q s b; norm_num [trivialNTM],
    by intro q s b; norm_num [trivialNTM]⟩

/-- The language of all words is in NP, so `InNP` is not vacuous. -/
theorem inNP_univ : InNP (fun _ => True) := by
  refine ⟨trivialNTM, fun _ => 0, trivialNTM_wf, by norm_num [trivialNTM],
    PolyBounded.const 0, fun w => ?_⟩
  constructor
  · intro _
    exact ⟨fun _ => false, rfl⟩
  · intro _
    trivial

end Frontier

import Mathlib

/-!
# CNF formulas and nondeterministic Turing machines

Basic definitions used in the Cook-Levin development: propositional literals,
clauses, CNF formulas and their evaluation, and a nondeterministic Turing machine
with a tape of finitely many cells.
-/

namespace Frontier

/-! ## CNF formulas -/

/-- A literal: a variable index together with a polarity. -/
structure Lit where
  var : ℕ
  pos : Bool
deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- Value of a literal under an assignment. -/
def litEval (σ : ℕ → Bool) (l : Lit) : Bool := if l.pos then σ l.var else !σ l.var

/-- Value of a clause under an assignment. -/
def clauseEval (σ : ℕ → Bool) (c : Clause) : Bool := c.any (litEval σ)

/-- Value of a CNF formula under an assignment. -/
def cnfEval (σ : ℕ → Bool) (φ : CNF) : Bool := φ.all (clauseEval σ)

/-- A CNF formula is satisfiable when some assignment makes it true. -/
def Satisfiable (φ : CNF) : Prop := ∃ σ, cnfEval σ φ = true

theorem clauseEval_eq_true {σ : ℕ → Bool} {c : Clause} :
    clauseEval σ c = true ↔ ∃ l ∈ c, litEval σ l = true := by
  simp [clauseEval]

theorem cnfEval_eq_true {σ : ℕ → Bool} {φ : CNF} :
    cnfEval σ φ = true ↔ ∀ c ∈ φ, clauseEval σ c = true := by
  simp [cnfEval]

theorem litEval_pos {σ : ℕ → Bool} {v : ℕ} : litEval σ ⟨v, true⟩ = σ v := rfl

theorem litEval_neg {σ : ℕ → Bool} {v : ℕ} : litEval σ ⟨v, false⟩ = !σ v := rfl


theorem clauseEval_append {σ : ℕ → Bool} {c d : Clause} :
    clauseEval σ (c ++ d) = (clauseEval σ c || clauseEval σ d) := by
  simp [clauseEval]

theorem cnfEval_append {σ : ℕ → Bool} {φ ψ : CNF} :
    cnfEval σ (φ ++ ψ) = (cnfEval σ φ && cnfEval σ ψ) := by
  simp [cnfEval]


/-! ## Nondeterministic Turing machines

We use a Turing machine with a tape of `N` cells (the head is clamped inside the
tape), states named by natural numbers `< nStates` and tape symbols named by
natural numbers `< nSymbols`.  Nondeterminism is binary and explicit: at each step
the machine reads a *choice bit*, and the transition function is a function of the
current state, the scanned symbol and that choice bit. -/

/-- Head movement direction. -/
inductive Dir
  | L | S | R
deriving DecidableEq, Repr

/-- Move the head, clamping at the two ends of the `N`-cell tape. -/
def moveHead (N i : ℕ) : Dir → ℕ
  | .L => i - 1
  | .S => i
  | .R => if i + 1 < N then i + 1 else i

theorem moveHead_lt {N i : ℕ} (h : i < N) (d : Dir) : moveHead N i d < N := by
  cases d <;> simp only [moveHead] <;> [omega; omega; (split_ifs <;> omega)]

/-- A nondeterministic Turing machine. -/
structure NTM where
  nStates : ℕ
  nSymbols : ℕ
  start : ℕ
  accept : ℕ
  δ : ℕ → ℕ → Bool → ℕ × ℕ × Dir

/-- Well-formedness: the distinguished states are states, and the transition
function returns states and symbols that are in range. -/
structure NTM.WF (M : NTM) : Prop where
  start_lt : M.start < M.nStates
  accept_lt : M.accept < M.nStates
  δ_state_lt : ∀ q s b, (M.δ q s b).1 < M.nStates
  δ_symbol_lt : ∀ q s b, (M.δ q s b).2.1 < M.nSymbols

/-- A configuration of the machine. -/
structure Config where
  state : ℕ
  head : ℕ
  tape : ℕ → ℕ

/-- One step of the machine, given a choice bit. -/
def NTM.step (M : NTM) (N : ℕ) (c : Config) (b : Bool) : Config :=
  { state := (M.δ c.state (c.tape c.head) b).1
    head := moveHead N c.head (M.δ c.state (c.tape c.head) b).2.2
    tape := fun j => if j = c.head then (M.δ c.state (c.tape c.head) b).2.1 else c.tape j }

/-- The configuration after `t` steps, following the choice sequence `bs`. -/
def NTM.run (M : NTM) (N : ℕ) (c : Config) (bs : ℕ → Bool) : ℕ → Config
  | 0 => c
  | t + 1 => M.step N (M.run N c bs t) (bs t)

/-- The initial configuration on input tape `x`. -/
def NTM.initConfig (M : NTM) (x : ℕ → ℕ) : Config :=
  { state := M.start, head := 0, tape := x }

/-- `M` accepts the input tape `x` in exactly `T` steps using `N` tape cells. -/
def NTM.AcceptsIn (M : NTM) (N T : ℕ) (x : ℕ → ℕ) : Prop :=
  ∃ bs : ℕ → Bool, (M.run N (M.initConfig x) bs T).state = M.accept

/-- A configuration is in range when its state, head and tape entries are. -/
structure Config.InRange (M : NTM) (N : ℕ) (c : Config) : Prop where
  state_lt : c.state < M.nStates
  head_lt : c.head < N
  tape_lt : ∀ i, c.tape i < M.nSymbols

theorem NTM.step_inRange {M : NTM} (hM : M.WF) {N : ℕ} {c : Config}
    (hc : c.InRange M N) (b : Bool) : (M.step N c b).InRange M N := by
  refine ⟨hM.δ_state_lt _ _ _, moveHead_lt hc.head_lt _, ?_⟩
  intro i
  by_cases h : i = c.head <;> simp [NTM.step, h, hM.δ_symbol_lt, hc.tape_lt]

theorem NTM.run_inRange {M : NTM} (hM : M.WF) {N : ℕ} {c : Config}
    (hc : c.InRange M N) (bs : ℕ → Bool) (t : ℕ) : (M.run N c bs t).InRange M N := by
  induction t with
  | zero => exact hc
  | succ t ih => exact NTM.step_inRange hM ih _

end Frontier

import RequestProject.Frontier.Correctness

/-!
# Size of the tableau formula

The number of clauses of the tableau is polynomially bounded in the tape length, the
time bound and the size of the machine.
-/

namespace Frontier

/-! ## Size of the tableau -/

theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    calc (f a).length + (l.flatMap f).length ≤ k + l.length * k := Nat.add_le_add h1 h2
      _ = (l.length + 1) * k := by ring

theorem length_gSymSome (M : NTM) (N T : ℕ) : (gSymSome M N T).length ≤ (T + 1) * N := by
  simp [gSymSome]

theorem length_gSymUnique (M : NTM) (N T : ℕ) :
    (gSymUnique M N T).length ≤ (T + 1) * (N * (M.nSymbols * M.nSymbols)) := by
  have hinner : ∀ t : ℕ,
      ((List.range N).flatMap fun i =>
        (List.range M.nSymbols).flatMap fun s =>
          (List.range s).map fun s' =>
            [(⟨vSym M N t i s, false⟩ : Lit), ⟨vSym M N t i s', false⟩]).length ≤
        N * (M.nSymbols * M.nSymbols) := by
    intro t
    refine le_trans (length_flatMap_le _ _ (M.nSymbols * M.nSymbols) ?_) (by simp)
    intro i _
    refine le_trans (length_flatMap_le _ _ M.nSymbols ?_) (by simp)
    intro s hs
    simp only [List.length_map, List.length_range]
    exact le_of_lt (List.mem_range.1 hs)
  have := length_flatMap_le (List.range (T + 1)) _ _ (fun t _ => hinner t)
  simpa [gSymUnique] using this

theorem length_gStateSome (M : NTM) (T : ℕ) : (gStateSome M T).length = T + 1 := by
  simp [gStateSome]

theorem length_gStateUnique (M : NTM) (T : ℕ) :
    (gStateUnique M T).length ≤ (T + 1) * (M.nStates * M.nStates) := by
  have hinner : ∀ t : ℕ,
      ((List.range M.nStates).flatMap fun q =>
        (List.range q).map fun q' =>
          [(⟨vState M t q, false⟩ : Lit), ⟨vState M t q', false⟩]).length ≤
        M.nStates * M.nStates := by
    intro t
    refine le_trans (length_flatMap_le _ _ M.nStates ?_) (by simp)
    intro q hq
    simp only [List.length_map, List.length_range]
    exact le_of_lt (List.mem_range.1 hq)
  have := length_flatMap_le (List.range (T + 1)) _ _ (fun t _ => hinner t)
  simpa [gStateUnique] using this

theorem length_gHeadSome (N T : ℕ) : (gHeadSome N T).length = T + 1 := by simp [gHeadSome]

theorem length_gHeadUnique (N T : ℕ) : (gHeadUnique N T).length ≤ (T + 1) * (N * N) := by
  have hinner : ∀ t : ℕ,
      ((List.range N).flatMap fun i =>
        (List.range i).map fun i' =>
          [(⟨vHead N t i, false⟩ : Lit), ⟨vHead N t i', false⟩]).length ≤ N * N := by
    intro t
    refine le_trans (length_flatMap_le _ _ N ?_) (by simp)
    intro i hi
    simp only [List.length_map, List.length_range]
    exact le_of_lt (List.mem_range.1 hi)
  have := length_flatMap_le (List.range (T + 1)) _ _ (fun t _ => hinner t)
  simpa [gHeadUnique] using this

theorem length_gInit (M : NTM) (N : ℕ) (x : ℕ → ℕ) : (gInit M N x).length = N + 2 := by
  simp [gInit]

theorem length_gAccept (M : NTM) (T : ℕ) : (gAccept M T).length = 1 := rfl

theorem length_gTrans (M : NTM) (N T : ℕ) :
    (gTrans M N T).length ≤ T * (N * (M.nStates * (M.nSymbols * 6))) := by
  simp [gTrans]

theorem length_gInertia (M : NTM) (N T : ℕ) :
    (gInertia M N T).length ≤ T * (N * M.nSymbols) := by
  simp [gInertia]

/-- A crude but polynomial bound on the number of clauses of the tableau. -/
theorem tableau_length_le (M : NTM) (N T : ℕ) (x : ℕ → ℕ) :
    (tableau M N T x).length ≤
      20 * ((T + 1) * (N + M.nStates + M.nSymbols + 1) ^ 3) := by
  set A := N + M.nStates + M.nSymbols + 1 with hA
  have hNA : N ≤ A := by omega
  have hQA : M.nStates ≤ A := by omega
  have hGA : M.nSymbols ≤ A := by omega
  have hA1 : 1 ≤ A := by omega
  have hA3 : A ^ 3 = A * A * A := by ring
  have hle1 : A ≤ A * A * A := by nlinarith
  have h1 : (T + 1) * N ≤ (T + 1) * (A ^ 3) := by
    exact Nat.mul_le_mul_left _ (le_trans hNA (by rw [hA3]; exact hle1))
  have h2 : (T + 1) * (N * (M.nSymbols * M.nSymbols)) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    rw [hA3]
    calc N * (M.nSymbols * M.nSymbols) ≤ A * (A * A) :=
          Nat.mul_le_mul hNA (Nat.mul_le_mul hGA hGA)
      _ = A * A * A := by ring
  have h3 : (T + 1) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.le_mul_of_pos_right _ ?_
    positivity
  have h4 : (T + 1) * (M.nStates * M.nStates) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    rw [hA3]
    calc M.nStates * M.nStates ≤ A * A := Nat.mul_le_mul hQA hQA
      _ ≤ A * A * A := by nlinarith
  have h5 : (T + 1) * (N * N) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    rw [hA3]
    calc N * N ≤ A * A := Nat.mul_le_mul hNA hNA
      _ ≤ A * A * A := by nlinarith
  have h6 : N + 2 + 1 ≤ 4 * ((T + 1) * (A ^ 3)) := by
    have : N ≤ (T + 1) * (A ^ 3) := le_trans (le_trans hNA (by rw [hA3]; exact hle1))
      (Nat.le_mul_of_pos_left _ (by omega))
    have h1' : 1 ≤ (T + 1) * (A ^ 3) := le_trans (by omega) h3
    omega
  have h7 : T * (N * (M.nStates * (M.nSymbols * 6))) ≤ 6 * ((T + 1) * (A ^ 3)) := by
    have hstep : N * (M.nStates * (M.nSymbols * 6)) ≤ 6 * (A ^ 3) := by
      rw [hA3]
      calc N * (M.nStates * (M.nSymbols * 6)) = 6 * (N * (M.nStates * M.nSymbols)) := by ring
        _ ≤ 6 * (A * (A * A)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hNA (Nat.mul_le_mul hQA hGA))
        _ = 6 * (A * A * A) := by ring
    calc T * (N * (M.nStates * (M.nSymbols * 6))) ≤ (T + 1) * (6 * (A ^ 3)) :=
          Nat.mul_le_mul (by omega) hstep
      _ = 6 * ((T + 1) * (A ^ 3)) := by ring
  have h8 : T * (N * M.nSymbols) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul (by omega) ?_
    rw [hA3]
    calc N * M.nSymbols ≤ A * A := Nat.mul_le_mul hNA hGA
      _ ≤ A * A * A := by nlinarith
  have hsum : (tableau M N T x).length ≤
      (T + 1) * N + (T + 1) * (N * (M.nSymbols * M.nSymbols)) + (T + 1) +
        (T + 1) * (M.nStates * M.nStates) + (T + 1) + (T + 1) * (N * N) + (N + 2) + 1 +
        T * (N * (M.nStates * (M.nSymbols * 6))) + T * (N * M.nSymbols) := by
    simp only [tableau, List.length_append, length_gStateSome, length_gHeadSome,
      length_gInit, length_gAccept]
    have a1 := length_gSymSome M N T
    have a2 := length_gSymUnique M N T
    have a4 := length_gStateUnique M T
    have a6 := length_gHeadUnique N T
    have a9 := length_gTrans M N T
    have a10 := length_gInertia M N T
    omega
  omega

end Frontier

import RequestProject.Frontier.Tableau

/-!
# Correctness of the tableau reduction

The tableau formula of a machine is satisfiable exactly when the machine has an
accepting computation of the prescribed length.
-/

namespace Frontier

/-! ## Completeness: an accepting run yields a satisfying assignment -/

section Complete

variable {M : NTM} (hM : M.WF) {N T : ℕ} (hN : 0 < N) {x : ℕ → ℕ}
  (hx : ∀ i, x i < M.nSymbols) (bs : ℕ → Bool)

private noncomputable def runOf (M : NTM) (N : ℕ) (x : ℕ → ℕ) (bs : ℕ → Bool) : ℕ → Config :=
  M.run N (M.initConfig x) bs

include hM hN hx in
private theorem runOf_inRange (t : ℕ) : (runOf M N x bs t).InRange M N :=
  NTM.run_inRange hM ⟨hM.start_lt, hN, hx⟩ bs t

include hM hN hx in
/-- The canonical assignment associated with an accepting run satisfies the tableau. -/
theorem tabAssign_sat_tableau
    (hacc : (runOf M N x bs T).state = M.accept) :
    cnfEval (tabAssign M N (runOf M N x bs) bs) (tableau M N T x) = true := by
  set R := runOf M N x bs with hR
  set σ := tabAssign M N R bs with hσ
  have hrange : ∀ t, (R t).InRange M N := runOf_inRange hM hN hx bs
  have hstep : ∀ t, R (t + 1) = M.step N (R t) (bs t) := fun t => rfl
  -- values of the assignment
  have hsym : ∀ t i s, s < M.nSymbols → i < N → σ (vSym M N t i s) = decide (s = (R t).tape i) :=
    fun t i s hs hi => tabAssign_vSym hs hi
  have hstate : ∀ t q, q < M.nStates → σ (vState M t q) = decide (q = (R t).state) :=
    fun t q hq => tabAssign_vState hq
  have hhead : ∀ t i, i < N → σ (vHead N t i) = decide (i = (R t).head) :=
    fun t i hi => tabAssign_vHead hi
  have hch : ∀ t, σ (vChoice t) = bs t := fun t => tabAssign_vChoice
  -- premise analysis for the transition clauses
  have hprem : ∀ t i q s b, i < N → q < M.nStates → s < M.nSymbols →
      clauseEval σ (transPrem M N t i q s b) = true ∨
        (i = (R t).head ∧ q = (R t).state ∧ s = (R t).tape i ∧ bs t = b) := by
    intro t i q s b hi hq hs
    by_cases h1 : i = (R t).head
    · by_cases h2 : q = (R t).state
      · by_cases h3 : s = (R t).tape i
        · by_cases h4 : bs t = b
          · exact Or.inr ⟨h1, h2, h3, h4⟩
          · refine Or.inl ?_
            rw [clauseEval_eq_true]
            refine ⟨⟨vChoice t, !b⟩, by simp [transPrem], ?_⟩
            cases b <;> simp [litEval, hch] at h4 ⊢ <;> simp [h4]
        · refine Or.inl ?_
          rw [clauseEval_eq_true]
          exact ⟨⟨vSym M N t i s, false⟩, by simp [transPrem], by simp [litEval, hsym t i s hs hi, h3]⟩
      · refine Or.inl ?_
        rw [clauseEval_eq_true]
        exact ⟨⟨vState M t q, false⟩, by simp [transPrem], by simp [litEval, hstate t q hq, h2]⟩
    · refine Or.inl ?_
      rw [clauseEval_eq_true]
      exact ⟨⟨vHead N t i, false⟩, by simp [transPrem], by simp [litEval, hhead t i hi, h1]⟩
  have hconcl : ∀ (c : Clause) (l : Lit), litEval σ l = true → clauseEval σ (c ++ [l]) = true := by
    intro c l hl
    rw [clauseEval_eq_true]
    exact ⟨l, by simp, hl⟩
  rw [tableau]
  simp only [cnfEval_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- gSymSome
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gSymSome, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, rfl⟩ := hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vSym M N t i ((R t).tape i), true⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(R t).tape i, List.mem_range.2 ((hrange t).tape_lt i), rfl⟩
    · simp [litEval, hsym t i _ ((hrange t).tape_lt i) hi]
  · -- gSymUnique
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gSymUnique, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, s, hs, s', hs', rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h : s = (R t).tape i
    · refine ⟨⟨vSym M N t i s', false⟩, by simp, ?_⟩
      have hs'' : s' < M.nSymbols := by omega
      simp [litEval, hsym t i s' hs'' hi]
      omega
    · exact ⟨⟨vSym M N t i s, false⟩, by simp, by simp [litEval, hsym t i s hs hi, h]⟩
  · -- gStateSome
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gStateSome, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vState M t (R t).state, true⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(R t).state, List.mem_range.2 (hrange t).state_lt, rfl⟩
    · simp [litEval, hstate t _ (hrange t).state_lt]
  · -- gStateUnique
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gStateUnique, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, q, hq, q', hq', rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h : q = (R t).state
    · refine ⟨⟨vState M t q', false⟩, by simp, ?_⟩
      have hq'' : q' < M.nStates := by omega
      simp [litEval, hstate t q' hq'']
      omega
    · exact ⟨⟨vState M t q, false⟩, by simp, by simp [litEval, hstate t q hq, h]⟩
  · -- gHeadSome
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gHeadSome, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vHead N t (R t).head, true⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(R t).head, List.mem_range.2 (hrange t).head_lt, rfl⟩
    · simp [litEval, hhead t _ (hrange t).head_lt]
  · -- gHeadUnique
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gHeadUnique, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, i', hi', rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h : i = (R t).head
    · refine ⟨⟨vHead N t i', false⟩, by simp, ?_⟩
      have hi'' : i' < N := by omega
      simp [litEval, hhead t i' hi'']
      omega
    · exact ⟨⟨vHead N t i, false⟩, by simp, by simp [litEval, hhead t i hi, h]⟩
  · -- gInit
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gInit, List.mem_cons, List.mem_map, List.mem_range] at hc
    have h0 : R 0 = M.initConfig x := rfl
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · rw [clauseEval_eq_true]
      refine ⟨⟨vState M 0 M.start, true⟩, by simp, ?_⟩
      rw [litEval_pos, hstate 0 _ hM.start_lt]
      simp [h0, NTM.initConfig]
    · rw [clauseEval_eq_true]
      refine ⟨⟨vHead N 0 0, true⟩, by simp, ?_⟩
      rw [litEval_pos, hhead 0 0 hN]
      simp [h0, NTM.initConfig]
    · rw [clauseEval_eq_true]
      refine ⟨⟨vSym M N 0 i (x i), true⟩, by simp, ?_⟩
      rw [litEval_pos, hsym 0 i _ (hx i) hi]
      simp [h0, NTM.initConfig]
  · -- gAccept
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gAccept, List.mem_singleton] at hc
    subst hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vState M T M.accept, true⟩, by simp, ?_⟩
    rw [litEval_pos, hstate T _ hM.accept_lt]
    simp [hacc]
  · -- gTrans
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gTrans, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    obtain ⟨t, ht, i, hi, q, hq, s, hs, b, -, hcc⟩ := hc
    rcases hprem t i q s b hi hq hs with hp | ⟨e1, e2, e3, e4⟩
    · rcases hcc with rfl | rfl | rfl <;> simp [clauseEval_append, hp]
    · have hR1 : R (t + 1) = M.step N (R t) b := by rw [hstep t, e4]
      subst e1; subst e2; subst e3
      rcases hcc with rfl | rfl | rfl
      · refine hconcl _ _ ?_
        rw [litEval_pos, hstate _ _ (hM.δ_state_lt _ _ _), hR1]
        simp [NTM.step]
      · refine hconcl _ _ ?_
        rw [litEval_pos, hsym _ _ _ (hM.δ_symbol_lt _ _ _) hi, hR1]
        simp [NTM.step]
      · refine hconcl _ _ ?_
        rw [litEval_pos, hhead _ _ (moveHead_lt hi _), hR1]
        simp [NTM.step]
  · -- gInertia
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gInertia, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, s, hs, rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h1 : i = (R t).head
    · refine ⟨⟨vHead N t i, true⟩, by simp, ?_⟩
      rw [litEval_pos, hhead t i hi]
      simp [h1]
    · by_cases h2 : s = (R t).tape i
      · refine ⟨⟨vSym M N (t + 1) i s, true⟩, by simp, ?_⟩
        rw [litEval_pos, hsym _ _ _ hs hi, hstep t]
        simp [NTM.step, h1, ← h2]
      · exact ⟨⟨vSym M N t i s, false⟩, by simp, by simp [litEval, hsym t i s hs hi, h2]⟩

end Complete

/-! ## Soundness: a satisfying assignment yields an accepting run -/

section Subsets

variable {M : NTM} {N T : ℕ} {x : ℕ → ℕ}

theorem gSymSome_sub : gSymSome M N T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gSymUnique_sub : gSymUnique M N T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gStateSome_sub : gStateSome M T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gStateUnique_sub : gStateUnique M T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gHeadSome_sub : gHeadSome N T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gHeadUnique_sub : gHeadUnique N T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gInit_sub : gInit M N x ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gAccept_sub : gAccept M T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gTrans_sub : gTrans M N T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

theorem gInertia_sub : gInertia M N T ⊆ tableau M N T x := by
  intro c hc; simp only [tableau, List.mem_append]; tauto

end Subsets

/-- If a clause `c ++ [l]` is satisfied but `c` is not, then the literal `l` is true. -/
theorem litEval_of_append {σ : ℕ → Bool} {c : Clause} {l : Lit}
    (h : clauseEval σ (c ++ [l]) = true) (hc : clauseEval σ c = false) : litEval σ l = true := by
  rw [clauseEval_append, hc, Bool.false_or] at h
  simpa [clauseEval] using h

/-- A satisfying assignment for the tableau yields an accepting computation. -/
theorem accepts_of_sat {M : NTM} (hM : M.WF) {N T : ℕ} (hN : 0 < N) {x : ℕ → ℕ}
    (hx : ∀ i, x i < M.nSymbols) {σ : ℕ → Bool} (hsat : cnfEval σ (tableau M N T x) = true) :
    M.AcceptsIn N T x := by
  have hall : ∀ c ∈ tableau M N T x, clauseEval σ c = true := cnfEval_eq_true.1 hsat
  set bs : ℕ → Bool := fun t => σ (vChoice t) with hbs
  set R : ℕ → Config := M.run N (M.initConfig x) bs with hRdef
  have hrange : ∀ t, (R t).InRange M N := fun t =>
    NTM.run_inRange hM ⟨hM.start_lt, hN, hx⟩ bs t
  have hstep : ∀ t, R (t + 1) = M.step N (R t) (bs t) := fun t => rfl
  -- "at least one" facts
  have symSome : ∀ t ≤ T, ∀ i < N, ∃ s, s < M.nSymbols ∧ σ (vSym M N t i s) = true := by
    intro t ht i hi
    have h := hall _ (gSymSome_sub (mem_gSymSome ht hi))
    rw [clauseEval_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := h
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    exact ⟨s, hs, by simpa [litEval] using hlv⟩
  have stateSome : ∀ t ≤ T, ∃ q, q < M.nStates ∧ σ (vState M t q) = true := by
    intro t ht
    have h := hall _ (gStateSome_sub (mem_gStateSome (M := M) ht))
    rw [clauseEval_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := h
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨q, hq, rfl⟩ := hl
    exact ⟨q, hq, by simpa [litEval] using hlv⟩
  have headSome : ∀ t ≤ T, ∃ i, i < N ∧ σ (vHead N t i) = true := by
    intro t ht
    have h := hall _ (gHeadSome_sub (M := M) (x := x) (mem_gHeadSome (N := N) ht))
    rw [clauseEval_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := h
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    exact ⟨i, hi, by simpa [litEval] using hlv⟩
  -- "at most one" facts
  have symUniq : ∀ t ≤ T, ∀ i < N, ∀ s < M.nSymbols, ∀ s' < M.nSymbols,
      σ (vSym M N t i s) = true → σ (vSym M N t i s') = true → s = s' := by
    intro t ht i hi s hs s' hs' h h'
    rcases lt_trichotomy s s' with hlt | heq | hgt
    · have hc := hall _ (gSymUnique_sub (mem_gSymUnique ht hi hs' hlt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
    · exact heq
    · have hc := hall _ (gSymUnique_sub (mem_gSymUnique ht hi hs hgt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
  have stateUniq : ∀ t ≤ T, ∀ q < M.nStates, ∀ q' < M.nStates,
      σ (vState M t q) = true → σ (vState M t q') = true → q = q' := by
    intro t ht q hq q' hq' h h'
    rcases lt_trichotomy q q' with hlt | heq | hgt
    · have hc := hall _ (gStateUnique_sub (mem_gStateUnique ht hq' hlt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
    · exact heq
    · have hc := hall _ (gStateUnique_sub (mem_gStateUnique ht hq hgt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
  have headUniq : ∀ t ≤ T, ∀ i < N, ∀ i' < N,
      σ (vHead N t i) = true → σ (vHead N t i') = true → i = i' := by
    intro t ht i hi i' hi' h h'
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · have hc := hall _ (gHeadUnique_sub (M := M) (x := x) (mem_gHeadUnique ht hi' hlt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
    · exact heq
    · have hc := hall _ (gHeadUnique_sub (M := M) (x := x) (mem_gHeadUnique ht hi hgt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
  -- the main induction
  have key : ∀ t, t ≤ T →
      (∀ q, q < M.nStates → σ (vState M t q) = true → q = (R t).state) ∧
      (∀ i, i < N → σ (vHead N t i) = true → i = (R t).head) ∧
      (∀ i, i < N → ∀ s, s < M.nSymbols → σ (vSym M N t i s) = true → s = (R t).tape i) := by
    intro t
    induction t with
    | zero =>
      intro _
      have h0 : R 0 = M.initConfig x := rfl
      have hst : σ (vState M 0 M.start) = true := by
        have hmem : [(⟨vState M 0 M.start, true⟩ : Lit)] ∈ gInit M N x := by simp [gInit]
        have hc := hall _ (gInit_sub (T := T) hmem)
        simpa [clauseEval, litEval] using hc
      have hhd : σ (vHead N 0 0) = true := by
        have hmem : [(⟨vHead N 0 0, true⟩ : Lit)] ∈ gInit M N x := by simp [gInit]
        have hc := hall _ (gInit_sub (T := T) hmem)
        simpa [clauseEval, litEval] using hc
      refine ⟨?_, ?_, ?_⟩
      · intro q hq h
        rw [h0]
        exact stateUniq 0 (Nat.zero_le _) q hq _ hM.start_lt h hst
      · intro i hi h
        rw [h0]
        exact headUniq 0 (Nat.zero_le _) i hi 0 hN h hhd
      · intro i hi s hs h
        have hmem : [(⟨vSym M N 0 i (x i), true⟩ : Lit)] ∈ gInit M N x := by
          simp only [gInit, List.mem_cons, List.mem_map, List.mem_range]
          exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
        have hc := hall _ (gInit_sub (T := T) hmem)
        have hxi : σ (vSym M N 0 i (x i)) = true := by simpa [clauseEval, litEval] using hc
        rw [h0]
        exact symUniq 0 (Nat.zero_le _) i hi s hs _ (hx i) h hxi
    | succ t ih =>
      intro ht1
      have ht : t < T := by omega
      have htle : t ≤ T := by omega
      obtain ⟨ihq, ihh, ihs⟩ := ih htle
      -- the true state/head/symbol at time `t` are asserted by the assignment
      have posQ : σ (vState M t (R t).state) = true := by
        obtain ⟨q, hq, hqv⟩ := stateSome t htle
        rwa [ihq q hq hqv] at hqv
      have posH : σ (vHead N t (R t).head) = true := by
        obtain ⟨i, hi, hiv⟩ := headSome t htle
        rwa [ihh i hi hiv] at hiv
      have posS : ∀ i, i < N → σ (vSym M N t i ((R t).tape i)) = true := by
        intro i hi
        obtain ⟨s, hs, hsv⟩ := symSome t htle i hi
        rwa [ihs i hi s hs hsv] at hsv
      have hpremfalse :
          clauseEval σ (transPrem M N t (R t).head (R t).state ((R t).tape (R t).head) (bs t))
            = false := by
        have hch : σ (vChoice t) = bs t := rfl
        cases hb : bs t <;>
          simp [clauseEval, transPrem, litEval, posQ, posH, posS _ (hrange t).head_lt, hch, hb]
      have hi0 : (R t).head < N := (hrange t).head_lt
      have hq0 : (R t).state < M.nStates := (hrange t).state_lt
      have hs0 : (R t).tape (R t).head < M.nSymbols := (hrange t).tape_lt _
      have hR1 : R (t + 1) = M.step N (R t) (bs t) := hstep t
      -- the three conclusions of the transition clauses
      have c1 : σ (vState M (t + 1) (R (t + 1)).state) = true := by
        have hc := hall _ (gTrans_sub (x := x) (mem_gTrans (b := bs t) ht hi0 hq0 hs0 (Or.inl rfl)))
        have := litEval_of_append hc hpremfalse
        rw [hR1]
        simpa [litEval, NTM.step] using this
      have c2 : σ (vSym M N (t + 1) (R t).head ((R (t + 1)).tape (R t).head)) = true := by
        have hc := hall _ (gTrans_sub (x := x) (mem_gTrans (b := bs t) ht hi0 hq0 hs0 (Or.inr (Or.inl rfl))))
        have := litEval_of_append hc hpremfalse
        rw [hR1]
        simpa [litEval, NTM.step] using this
      have c3 : σ (vHead N (t + 1) (R (t + 1)).head) = true := by
        have hc := hall _
          (gTrans_sub (x := x) (mem_gTrans (b := bs t) ht hi0 hq0 hs0 (Or.inr (Or.inr rfl))))
        have := litEval_of_append hc hpremfalse
        rw [hR1]
        simpa [litEval, NTM.step] using this
      have hstate1 : (R (t + 1)).state < M.nStates := (hrange (t + 1)).state_lt
      have hhead1 : (R (t + 1)).head < N := (hrange (t + 1)).head_lt
      refine ⟨?_, ?_, ?_⟩
      · intro q hq h
        exact stateUniq (t + 1) ht1 q hq _ hstate1 h c1
      · intro i hi h
        exact headUniq (t + 1) ht1 i hi _ hhead1 h c3
      · intro i hi s hs h
        by_cases hie : i = (R t).head
        · subst hie
          exact symUniq (t + 1) ht1 _ hi s hs _ ((hrange (t + 1)).tape_lt _) h c2
        · have hne : σ (vHead N t i) = false := by
            by_contra hcon
            exact hie (ihh i hi (by simpa using hcon))
          have hc := hall _ (gInertia_sub (x := x) (mem_gInertia ht hi ((hrange t).tape_lt i)))
          rw [clauseEval_eq_true] at hc
          obtain ⟨l, hl, hlv⟩ := hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          have hkeep : σ (vSym M N (t + 1) i ((R t).tape i)) = true := by
            rcases hl with rfl | rfl | rfl
            · simp [litEval, hne] at hlv
            · simp [litEval, posS i hi] at hlv
            · simpa [litEval] using hlv
          have htape : (R (t + 1)).tape i = (R t).tape i := by
            rw [hR1]; simp [NTM.step, hie]
          rw [htape]
          exact symUniq (t + 1) ht1 i hi s hs _ ((hrange t).tape_lt i) h hkeep
  -- conclude from the accepting clause
  refine ⟨bs, ?_⟩
  have hmemacc : [(⟨vState M T M.accept, true⟩ : Lit)] ∈ gAccept M T := by simp [gAccept]
  have hc := hall _ (gAccept_sub (N := N) (x := x) hmemacc)
  have hacc : σ (vState M T M.accept) = true := by simpa [clauseEval, litEval] using hc
  exact ((key T le_rfl).1 M.accept hM.accept_lt hacc).symm

/-! ## The main equivalence -/

/-- **The Cook–Levin tableau theorem.**  The explicitly constructed CNF formula
`tableau M N T x` is satisfiable if and only if the nondeterministic machine `M`,
run on the tape `x` with `N` cells, has an accepting computation of length `T`. -/
theorem tableau_satisfiable_iff {M : NTM} (hM : M.WF) {N T : ℕ} (hN : 0 < N) {x : ℕ → ℕ}
    (hx : ∀ i, x i < M.nSymbols) :
    Satisfiable (tableau M N T x) ↔ M.AcceptsIn N T x := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact accepts_of_sat hM hN hx hσ
  · rintro ⟨bs, hacc⟩
    exact ⟨_, tabAssign_sat_tableau hM hN hx bs hacc⟩

end Frontier

import RequestProject.Frontier.Basic

/-!
# The Cook-Levin tableau formula

The propositional variables of the tableau, the canonical assignment attached to a
run, the clause groups making up the tableau, and membership lemmas for them.
-/

namespace Frontier

/-! ## Encoding the tableau variables

The tableau uses four families of propositional variables:

* `vSym M N t i s` : at time `t`, cell `i` carries symbol `s`;
* `vState M t q`   : at time `t` the machine is in state `q`;
* `vHead N t i`    : at time `t` the head scans cell `i`;
* `vChoice t`      : the nondeterministic choice bit used at step `t`.

They are encoded as natural numbers via an explicit injective pairing. -/

/-- Variable saying that at time `t`, cell `i` carries symbol `s`. -/
def vSym (M : NTM) (N t i s : ℕ) : ℕ := 4 * (s + M.nSymbols * (i + N * t))

/-- Variable saying that at time `t` the machine is in state `q`. -/
def vState (M : NTM) (t q : ℕ) : ℕ := 4 * (q + M.nStates * t) + 1

/-- Variable saying that at time `t` the head scans cell `i`. -/
def vHead (N t i : ℕ) : ℕ := 4 * (i + N * t) + 2

/-- Variable holding the nondeterministic choice bit used at step `t`. -/
def vChoice (t : ℕ) : ℕ := 4 * t + 3

/-- The canonical assignment attached to a sequence of configurations `R` and a
sequence of choice bits `bs`. -/
def tabAssign (M : NTM) (N : ℕ) (R : ℕ → Config) (bs : ℕ → Bool) (v : ℕ) : Bool :=
  if v % 4 = 0 then
    decide (v / 4 % M.nSymbols = (R (v / 4 / M.nSymbols / N)).tape (v / 4 / M.nSymbols % N))
  else if v % 4 = 1 then decide (v / 4 % M.nStates = (R (v / 4 / M.nStates)).state)
  else if v % 4 = 2 then decide (v / 4 % N = (R (v / 4 / N)).head)
  else bs (v / 4)

private theorem pair_mod {a b n : ℕ} (h : a < n) : (a + n * b) % n = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

private theorem pair_div {a b n : ℕ} (h : a < n) : (a + n * b) / n = b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h
  rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt h, Nat.zero_add]

@[simp] theorem tabAssign_vSym {M : NTM} {N : ℕ} {R : ℕ → Config} {bs : ℕ → Bool}
    {t i s : ℕ} (hs : s < M.nSymbols) (hi : i < N) :
    tabAssign M N R bs (vSym M N t i s) = decide (s = (R t).tape i) := by
  have h4 : (0:ℕ) < 4 := by norm_num
  simp only [tabAssign, vSym, Nat.mul_mod_right, Nat.mul_div_cancel_left _ h4]
  rw [pair_mod hs, pair_div hs, pair_mod hi, pair_div hi]
  simp

@[simp] theorem tabAssign_vState {M : NTM} {N : ℕ} {R : ℕ → Config} {bs : ℕ → Bool}
    {t q : ℕ} (hq : q < M.nStates) :
    tabAssign M N R bs (vState M t q) = decide (q = (R t).state) := by
  have h1 : (4 * (q + M.nStates * t) + 1) % 4 = 1 := by omega
  have h2 : (4 * (q + M.nStates * t) + 1) / 4 = q + M.nStates * t := by omega
  simp only [tabAssign, vState, h1, h2]
  norm_num
  rw [pair_div hq, Nat.mod_eq_of_lt hq]

@[simp] theorem tabAssign_vHead {M : NTM} {N : ℕ} {R : ℕ → Config} {bs : ℕ → Bool}
    {t i : ℕ} (hi : i < N) :
    tabAssign M N R bs (vHead N t i) = decide (i = (R t).head) := by
  have h1 : (4 * (i + N * t) + 2) % 4 = 2 := by omega
  have h2 : (4 * (i + N * t) + 2) / 4 = i + N * t := by omega
  simp only [tabAssign, vHead, h1, h2]
  norm_num
  rw [pair_div hi, Nat.mod_eq_of_lt hi]

@[simp] theorem tabAssign_vChoice {M : NTM} {N : ℕ} {R : ℕ → Config} {bs : ℕ → Bool}
    {t : ℕ} : tabAssign M N R bs (vChoice t) = bs t := by
  have h1 : (4 * t + 3) % 4 = 3 := by omega
  have h2 : (4 * t + 3) / 4 = t := by omega
  simp only [tabAssign, vChoice, h1, h2]
  norm_num

/-! ## The tableau formula -/

/-- "At each time and cell, some symbol is present." -/
def gSymSome (M : NTM) (N T : ℕ) : CNF :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range N).map fun i =>
      (List.range M.nSymbols).map fun s => (⟨vSym M N t i s, true⟩ : Lit)

/-- "At each time and cell, at most one symbol is present." -/
def gSymUnique (M : NTM) (N T : ℕ) : CNF :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range N).flatMap fun i =>
      (List.range M.nSymbols).flatMap fun s =>
        (List.range s).map fun s' =>
          [(⟨vSym M N t i s, false⟩ : Lit), ⟨vSym M N t i s', false⟩]

/-- "At each time the machine is in some state." -/
def gStateSome (M : NTM) (T : ℕ) : CNF :=
  (List.range (T + 1)).map fun t =>
    (List.range M.nStates).map fun q => (⟨vState M t q, true⟩ : Lit)

/-- "At each time the machine is in at most one state." -/
def gStateUnique (M : NTM) (T : ℕ) : CNF :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range M.nStates).flatMap fun q =>
      (List.range q).map fun q' =>
        [(⟨vState M t q, false⟩ : Lit), ⟨vState M t q', false⟩]

/-- "At each time the head is somewhere." -/
def gHeadSome (N T : ℕ) : CNF :=
  (List.range (T + 1)).map fun t =>
    (List.range N).map fun i => (⟨vHead N t i, true⟩ : Lit)

/-- "At each time the head is in at most one place." -/
def gHeadUnique (N T : ℕ) : CNF :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range N).flatMap fun i =>
      (List.range i).map fun i' =>
        [(⟨vHead N t i, false⟩ : Lit), ⟨vHead N t i', false⟩]

/-- The initial configuration is described correctly. -/
def gInit (M : NTM) (N : ℕ) (x : ℕ → ℕ) : CNF :=
  [(⟨vState M 0 M.start, true⟩ : Lit)] :: [(⟨vHead N 0 0, true⟩ : Lit)] ::
    ((List.range N).map fun i => [(⟨vSym M N 0 i (x i), true⟩ : Lit)])

/-- The final state is accepting. -/
def gAccept (M : NTM) (T : ℕ) : CNF := [[(⟨vState M T M.accept, true⟩ : Lit)]]

/-- The premise literals of a transition clause: "at time `t` the head is at `i`,
the state is `q`, cell `i` holds `s`, and the choice bit is `b`", negated. -/
def transPrem (M : NTM) (N t i q s : ℕ) (b : Bool) : Clause :=
  [⟨vHead N t i, false⟩, ⟨vState M t q, false⟩, ⟨vSym M N t i s, false⟩, ⟨vChoice t, !b⟩]

/-- The transition clauses. -/
def gTrans (M : NTM) (N T : ℕ) : CNF :=
  (List.range T).flatMap fun t =>
    (List.range N).flatMap fun i =>
      (List.range M.nStates).flatMap fun q =>
        (List.range M.nSymbols).flatMap fun s =>
          [false, true].flatMap fun b =>
            [transPrem M N t i q s b ++ [⟨vState M (t + 1) (M.δ q s b).1, true⟩],
             transPrem M N t i q s b ++ [⟨vSym M N (t + 1) i (M.δ q s b).2.1, true⟩],
             transPrem M N t i q s b ++
               [⟨vHead N (t + 1) (moveHead N i (M.δ q s b).2.2), true⟩]]

/-- Cells not scanned by the head do not change. -/
def gInertia (M : NTM) (N T : ℕ) : CNF :=
  (List.range T).flatMap fun t =>
    (List.range N).flatMap fun i =>
      (List.range M.nSymbols).map fun s =>
        [(⟨vHead N t i, true⟩ : Lit), ⟨vSym M N t i s, false⟩, ⟨vSym M N (t + 1) i s, true⟩]

/-- The Cook–Levin tableau formula for machine `M`, tape length `N`, time bound `T`
and input tape `x`. -/
def tableau (M : NTM) (N T : ℕ) (x : ℕ → ℕ) : CNF :=
  gSymSome M N T ++ gSymUnique M N T ++ gStateSome M T ++ gStateUnique M T ++
    gHeadSome N T ++ gHeadUnique N T ++ gInit M N x ++ gAccept M T ++
    gTrans M N T ++ gInertia M N T

/-! ### Membership lemmas -/

theorem mem_gSymSome {M : NTM} {N T t i : ℕ} (ht : t ≤ T) (hi : i < N) :
    ((List.range M.nSymbols).map fun s => (⟨vSym M N t i s, true⟩ : Lit)) ∈ gSymSome M N T := by
  simp only [gSymSome, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨t, by omega, i, hi, rfl⟩

theorem mem_gSymUnique {M : NTM} {N T t i s s' : ℕ} (ht : t ≤ T) (hi : i < N)
    (hs : s < M.nSymbols) (hs' : s' < s) :
    [(⟨vSym M N t i s, false⟩ : Lit), ⟨vSym M N t i s', false⟩] ∈ gSymUnique M N T := by
  simp only [gSymUnique, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨t, by omega, i, hi, s, hs, s', hs', rfl⟩

theorem mem_gStateSome {M : NTM} {T t : ℕ} (ht : t ≤ T) :
    ((List.range M.nStates).map fun q => (⟨vState M t q, true⟩ : Lit)) ∈ gStateSome M T := by
  simp only [gStateSome, List.mem_map, List.mem_range]
  exact ⟨t, by omega, rfl⟩

theorem mem_gStateUnique {M : NTM} {T t q q' : ℕ} (ht : t ≤ T) (hq : q < M.nStates)
    (hq' : q' < q) :
    [(⟨vState M t q, false⟩ : Lit), ⟨vState M t q', false⟩] ∈ gStateUnique M T := by
  simp only [gStateUnique, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨t, by omega, q, hq, q', hq', rfl⟩

theorem mem_gHeadSome {N T t : ℕ} (ht : t ≤ T) :
    ((List.range N).map fun i => (⟨vHead N t i, true⟩ : Lit)) ∈ gHeadSome N T := by
  simp only [gHeadSome, List.mem_map, List.mem_range]
  exact ⟨t, by omega, rfl⟩

theorem mem_gHeadUnique {N T t i i' : ℕ} (ht : t ≤ T) (hi : i < N) (hi' : i' < i) :
    [(⟨vHead N t i, false⟩ : Lit), ⟨vHead N t i', false⟩] ∈ gHeadUnique N T := by
  simp only [gHeadUnique, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨t, by omega, i, hi, i', hi', rfl⟩

theorem mem_gTrans {M : NTM} {N T t i q s : ℕ} {b : Bool} (ht : t < T) (hi : i < N)
    (hq : q < M.nStates) (hs : s < M.nSymbols) {c : Clause}
    (hc : c = transPrem M N t i q s b ++ [⟨vState M (t + 1) (M.δ q s b).1, true⟩] ∨
          c = transPrem M N t i q s b ++ [⟨vSym M N (t + 1) i (M.δ q s b).2.1, true⟩] ∨
          c = transPrem M N t i q s b ++
              [⟨vHead N (t + 1) (moveHead N i (M.δ q s b).2.2), true⟩]) :
    c ∈ gTrans M N T := by
  simp only [gTrans, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false]
  refine ⟨t, ht, i, hi, q, hq, s, hs, b, ?_, ?_⟩
  · cases b <;> simp
  · rcases hc with h | h | h <;> simp [h]

theorem mem_gInertia {M : NTM} {N T t i s : ℕ} (ht : t < T) (hi : i < N) (hs : s < M.nSymbols) :
    [(⟨vHead N t i, true⟩ : Lit), ⟨vSym M N t i s, false⟩, ⟨vSym M N (t + 1) i s, true⟩] ∈
      gInertia M N T := by
  simp only [gInertia, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨t, ht, i, hi, s, hs, rfl⟩

end Frontier

