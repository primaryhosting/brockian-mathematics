import Mathlib

/-!
# A model of relativized (oracle) polynomial-time computation

We fix a small imperative programming language over string-valued registers,
with an oracle-query primitive and a nondeterministic guess primitive, and an
explicit step-cost semantics.  This is the machine model used to define the
relativized classes `P^O` and `NP^O`.
-/

namespace BGS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings (given as a predicate). -/
abbrev Oracle := Str → Prop

/-- A register file: countably many string-valued registers. -/
abbrev Regs := ℕ → Str

/-- Update a register. -/
def upd (σ : Regs) (i : ℕ) (v : Str) : Regs := Function.update σ i v

@[simp] theorem upd_self (σ : Regs) (i : ℕ) (v : Str) : upd σ i v i = v := by
  simp [upd]

@[simp] theorem upd_other (σ : Regs) (i j : ℕ) (v : Str) (h : j ≠ i) :
    upd σ i v j = σ j := by
  simp [upd, Function.update_of_ne h]

/-- Programs of the model.

* `pushBit i b` appends the bit `b` to register `i` (cost `1`);
* `tail i` drops the first bit of register `i` (cost `1`);
* `clear i` empties register `i` (cost `1`);
* `app i j` appends the contents of register `j` to register `i`
  (cost `1 + |reg j|`, i.e. one unit per copied bit);
* `query i j` queries the oracle on the contents of register `j` and stores the
  answer bit in register `i` (cost `1`);
* `guess i` appends a nondeterministically chosen bit to register `i` (cost `1`);
* `seq`, `whileNE i s` (loop while register `i` is nonempty) and
  `ifTrue i s t` (branch on whether register `i` starts with the bit `true`)
  are the usual control structures (cost `1` per test). -/
inductive Stmt : Type
  | noop : Stmt
  | pushBit (i : ℕ) (b : Bool) : Stmt
  | tail (i : ℕ) : Stmt
  | clear (i : ℕ) : Stmt
  | app (i j : ℕ) : Stmt
  | query (i j : ℕ) : Stmt
  | guess (i : ℕ) : Stmt
  | seq (s t : Stmt) : Stmt
  | whileNE (i : ℕ) (s : Stmt) : Stmt
  | ifTrue (i : ℕ) (s t : Stmt) : Stmt

deriving instance Countable for Stmt

instance : Inhabited Stmt := ⟨Stmt.clear 0⟩

/-- A program is deterministic when it contains no `guess`. -/
def NoGuess : Stmt → Prop
  | .guess _ => False
  | .seq s t => NoGuess s ∧ NoGuess t
  | .whileNE _ s => NoGuess s
  | .ifTrue _ s t => NoGuess s ∧ NoGuess t
  | _ => True

/-- Big-step semantics: `Exec O s σ σ' c tr` says that, with oracle `O`, the
program `s` started in register file `σ` can terminate in register file `σ'`,
using `c` steps and asking exactly the oracle queries listed in `tr`. -/
inductive Exec (O : Oracle) : Stmt → Regs → Regs → ℕ → List Str → Prop
  | noop {σ} : Exec O .noop σ σ 1 []
  | pushBit {i b σ} : Exec O (.pushBit i b) σ (upd σ i (σ i ++ [b])) 1 []
  | tail {i σ} : Exec O (.tail i) σ (upd σ i (σ i).tail) 1 []
  | clear {i σ} : Exec O (.clear i) σ (upd σ i []) 1 []
  | app {i j σ} : Exec O (.app i j) σ (upd σ i (σ i ++ σ j)) (1 + (σ j).length) []
  | query {i j σ} (b : Bool) (h : O (σ j) ↔ b = true) :
      Exec O (.query i j) σ (upd σ i [b]) 1 [σ j]
  | guess {i σ} (b : Bool) : Exec O (.guess i) σ (upd σ i (σ i ++ [b])) 1 []
  | seq {s t σ σ' σ'' c c' tr tr'} : Exec O s σ σ' c tr → Exec O t σ' σ'' c' tr' →
      Exec O (.seq s t) σ σ'' (c + c') (tr ++ tr')
  | whileF {i s σ} (h : σ i = []) : Exec O (.whileNE i s) σ σ 1 []
  | whileT {i s σ σ' σ'' c c' tr tr'} (h : σ i ≠ []) :
      Exec O s σ σ' c tr → Exec O (.whileNE i s) σ' σ'' c' tr' →
      Exec O (.whileNE i s) σ σ'' (1 + c + c') (tr ++ tr')
  | ifT {i s t σ σ' c tr} (h : (σ i).head? = some true) : Exec O s σ σ' c tr →
      Exec O (.ifTrue i s t) σ σ' (1 + c) tr
  | ifF {i s t σ σ' c tr} (h : (σ i).head? ≠ some true) : Exec O t σ σ' c tr →
      Exec O (.ifTrue i s t) σ σ' (1 + c) tr

/-- The initial register file on input `x`: the input sits in register `0`. -/
def init (x : Str) : Regs := fun i => if i = 0 then x else []

@[simp] theorem init_zero (x : Str) : init x 0 = x := by simp [init]

theorem init_len (x : Str) (i : ℕ) : (init x i).length ≤ x.length := by
  by_cases h : i = 0 <;> simp [init, h]

/-- A register file is accepting when register `1` starts with the bit `true`. -/
def Acc (σ : Regs) : Prop := (σ 1).head? = some true

/-- `s` has an accepting run on `x` within `t` steps, relative to `O`. -/
def AcceptsIn (O : Oracle) (s : Stmt) (t : ℕ) (x : Str) : Prop :=
  ∃ σ' c tr, Exec O s (init x) σ' c tr ∧ c ≤ t ∧ Acc σ'

/-- The class `NP^O`. -/
def inNP (O : Oracle) (L : Str → Prop) : Prop :=
  ∃ (s : Stmt) (k : ℕ), ∀ x, (L x ↔ AcceptsIn O s ((x.length + 2) ^ k) x)

/-- The class `P^O`. -/
def inP (O : Oracle) (L : Str → Prop) : Prop :=
  ∃ (s : Stmt) (k : ℕ), NoGuess s ∧ ∀ x, ∃ σ' c tr,
    Exec O s (init x) σ' c tr ∧ c ≤ (x.length + 2) ^ k ∧ (Acc σ' ↔ L x)

/-! ### Basic properties of the semantics -/

/-- Deterministic programs have unique runs. -/
theorem Exec.det {O : Oracle} {s : Stmt} (hs : NoGuess s) {σ σ₁ σ₂ : Regs}
    {c₁ c₂ : ℕ} {tr₁ tr₂ : List Str}
    (h₁ : Exec O s σ σ₁ c₁ tr₁) (h₂ : Exec O s σ σ₂ c₂ tr₂) :
    σ₁ = σ₂ ∧ c₁ = c₂ ∧ tr₁ = tr₂ := by
  induction h₁ generalizing σ₂ c₂ tr₂ with
  | noop => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | pushBit => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | tail => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | clear => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | app => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | query b h =>
      cases h₂ with
      | query b' h' =>
          have : b = b' := by
            cases b <;> cases b' <;> simp_all
          subst this; exact ⟨rfl, rfl, rfl⟩
  | guess b => exact absurd hs (by simp [NoGuess])
  | seq e₁ e₂ ih₁ ih₂ =>
      cases h₂ with
      | seq f₁ f₂ =>
          obtain ⟨hσ, hc, htr⟩ := ih₁ hs.1 f₁
          subst hσ
          obtain ⟨hσ', hc', htr'⟩ := ih₂ hs.2 f₂
          exact ⟨hσ', by omega, by rw [htr, htr']⟩
  | whileF h =>
      cases h₂ with
      | whileF h' => exact ⟨rfl, rfl, rfl⟩
      | whileT h' _ _ => exact absurd h h'
  | whileT h e₁ e₂ ih₁ ih₂ =>
      cases h₂ with
      | whileF h' => exact absurd h' h
      | whileT h' f₁ f₂ =>
          obtain ⟨hσ, hc, htr⟩ := ih₁ hs f₁
          subst hσ
          obtain ⟨hσ', hc', htr'⟩ := ih₂ hs f₂
          exact ⟨hσ', by omega, by rw [htr, htr']⟩
  | ifT h e ih =>
      cases h₂ with
      | ifT h' f =>
          obtain ⟨hσ, hc, htr⟩ := ih hs.1 f
          exact ⟨hσ, by omega, htr⟩
      | ifF h' f => exact absurd h h'
  | ifF h e ih =>
      cases h₂ with
      | ifT h' f => exact absurd h' h
      | ifF h' f =>
          obtain ⟨hσ, hc, htr⟩ := ih hs.2 f
          exact ⟨hσ, by omega, htr⟩

/-- A run only depends on the oracle through the answers to the queries it
actually asks. -/
theorem Exec.locality {O O' : Oracle} {s : Stmt} {σ σ' : Regs} {c : ℕ} {tr : List Str}
    (h : Exec O s σ σ' c tr) (hagree : ∀ q ∈ tr, (O q ↔ O' q)) :
    Exec O' s σ σ' c tr := by
  induction h with
  | noop => exact Exec.noop
  | pushBit => exact Exec.pushBit
  | tail => exact Exec.tail
  | clear => exact Exec.clear
  | app => exact Exec.app
  | @query i j σ b h =>
      refine Exec.query b ?_
      have := hagree (σ j) (List.mem_singleton_self _)
      tauto
  | guess b => exact Exec.guess b
  | seq e₁ e₂ ih₁ ih₂ =>
      exact Exec.seq (ih₁ fun q hq => hagree q (by simp [hq]))
        (ih₂ fun q hq => hagree q (by simp [hq]))
  | whileF h => exact Exec.whileF h
  | whileT h e₁ e₂ ih₁ ih₂ =>
      exact Exec.whileT h (ih₁ fun q hq => hagree q (by simp [hq]))
        (ih₂ fun q hq => hagree q (by simp [hq]))
  | ifT h e ih => exact Exec.ifT h (ih hagree)
  | ifF h e ih => exact Exec.ifF h (ih hagree)

/-- The number of queries asked is at most the running time. -/
theorem Exec.trace_length {O : Oracle} {s : Stmt} {σ σ' : Regs} {c : ℕ} {tr : List Str}
    (h : Exec O s σ σ' c tr) : tr.length ≤ c := by
  induction h with
  | seq e₁ e₂ ih₁ ih₂ => simp only [List.length_append]; omega
  | whileT h e₁ e₂ ih₁ ih₂ => simp only [List.length_append]; omega
  | ifT h e ih => omega
  | ifF h e ih => omega
  | _ => simp

/-- Registers grow by at most one bit per step; in particular every queried
string is short. -/
theorem Exec.len_bound {O : Oracle} {s : Stmt} {σ σ' : Regs} {c : ℕ} {tr : List Str}
    (h : Exec O s σ σ' c tr) {L : ℕ} (hL : ∀ i, (σ i).length ≤ L) :
    (∀ i, (σ' i).length ≤ L + c) ∧ (∀ q ∈ tr, q.length ≤ L + c) := by
  induction h generalizing L with
  | noop => exact ⟨fun i => by have := hL i; omega, by simp⟩
  | @pushBit i b σ =>
      refine ⟨fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simp only [upd_self, List.length_append, List.length_cons,
          List.length_nil]; have := hL j; omega
      · rw [upd_other _ _ _ _ hj]; have := hL j; omega
  | @tail i σ =>
      refine ⟨fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simp only [upd_self]
        have := hL j
        have : (σ j).tail.length ≤ (σ j).length := by
          cases σ j <;> simp
        omega
      · rw [upd_other _ _ _ _ hj]; have := hL j; omega
  | @clear i σ =>
      refine ⟨fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simp
      · rw [upd_other _ _ _ _ hj]; have := hL j; omega
  | @app i j σ =>
      refine ⟨fun l => ?_, by simp⟩
      by_cases hl : l = i
      · subst hl; simp only [upd_self, List.length_append]
        have h1 := hL l; have h2 := hL j; omega
      · rw [upd_other _ _ _ _ hl]; have := hL l; omega
  | @query i j σ b h =>
      refine ⟨fun l => ?_, ?_⟩
      · by_cases hl : l = i
        · subst hl; simp
        · rw [upd_other _ _ _ _ hl]; have := hL l; omega
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst hq; have := hL j; omega
  | @guess i σ b =>
      refine ⟨fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simp only [upd_self, List.length_append, List.length_cons,
          List.length_nil]; have := hL j; omega
      · rw [upd_other _ _ _ _ hj]; have := hL j; omega
  | seq e₁ e₂ ih₁ ih₂ =>
      obtain ⟨hA, hB⟩ := ih₁ hL
      obtain ⟨hC, hD⟩ := ih₂ hA
      refine ⟨fun i => by have := hC i; omega, ?_⟩
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · have := hB q hq; omega
      · have := hD q hq; omega
  | whileF h => exact ⟨fun i => by have := hL i; omega, by simp⟩
  | whileT h e₁ e₂ ih₁ ih₂ =>
      obtain ⟨hA, hB⟩ := ih₁ hL
      obtain ⟨hC, hD⟩ := ih₂ hA
      refine ⟨fun i => by have := hC i; omega, ?_⟩
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · have := hB q hq; omega
      · have := hD q hq; omega
  | ifT h e ih =>
      obtain ⟨hA, hB⟩ := ih hL
      exact ⟨fun i => by have := hA i; omega, fun q hq => by have := hB q hq; omega⟩
  | ifF h e ih =>
      obtain ⟨hA, hB⟩ := ih hL
      exact ⟨fun i => by have := hA i; omega, fun q hq => by have := hB q hq; omega⟩

/-- Every string queried during a `c`-step run on input `x` has length at most
`|x| + c`. -/
theorem Exec.query_len {O : Oracle} {s : Stmt} {x : Str} {σ' : Regs} {c : ℕ} {tr : List Str}
    (h : Exec O s (init x) σ' c tr) : ∀ q ∈ tr, q.length ≤ x.length + c :=
  (h.len_bound (L := x.length) (init_len x)).2

/-- `P^O ⊆ NP^O`. -/
theorem inP_imp_inNP {O : Oracle} {L : Str → Prop} (h : inP O L) : inNP O L := by
  obtain ⟨s, k, hng, hs⟩ := h
  refine ⟨s, k, fun x => ?_⟩
  obtain ⟨σ', c, tr, hrun, hc, hacc⟩ := hs x
  constructor
  · intro hL
    exact ⟨σ', c, tr, hrun, hc, hacc.2 hL⟩
  · rintro ⟨σ'', c', tr', hrun', hc', hacc'⟩
    obtain ⟨e1, e2, e3⟩ := Exec.det hng hrun' hrun
    exact hacc.1 (e1 ▸ hacc')

end BGS

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

