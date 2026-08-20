/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean requires `import` before any
-- module docstring `/-! ... -/`.)

import Mathlib

/-!
## Overview

We formalize Tarski's undefinability theorem: the set of (Gödel numbers of) true
sentences of arithmetic is not itself definable by an arithmetical formula.

Everything is built from scratch:

* `Frontier.Tm` — terms of the language of arithmetic (variables, numerals, `+`, `*`);
* `Frontier.Fm` — formulas (equations, negation, conjunction, existential quantification);
* `Frontier.Tm.eval`, `Frontier.Fm.Sat` — the standard-model semantics over `ℕ`;
* `Frontier.Fm.freeVars` — free variables, so that "sentence" is meaningful;
* `Frontier.Fm.enc` — an injective Gödel numbering;
* `Frontier.TruthSet` — the set of Gödel numbers of true sentences of arithmetic;
* `Frontier.Definable` — definability of a set of naturals by an arithmetical formula.

The main theorem `Frontier.Tarski_undefinability` states `¬ Definable TruthSet`.
-/

namespace Frontier

/-! ### A polynomial pairing function -/

/-- A polynomial (twice-Cantor) pairing function on `ℕ`. -/
def pairP (a b : ℕ) : ℕ := (a + b) * (a + b + 1) + 2 * a

theorem pairP_inj {a b c d : ℕ} (h : pairP a b = pairP c d) : a = c ∧ b = d := by
  unfold pairP at h
  have hs : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with h1 | h1 | h1
    · nlinarith
    · exact h1
    · nlinarith
  rw [hs] at h
  omega

/-! ### Syntax -/

/-- Terms of the language of arithmetic: variables, numerals, sums and products. -/
inductive Tm where
  | var : ℕ → Tm
  | num : ℕ → Tm
  | add : Tm → Tm → Tm
  | mul : Tm → Tm → Tm
deriving DecidableEq

/-- Formulas of the language of arithmetic: equations between terms, closed under
negation, conjunction and existential quantification. -/
inductive Fm where
  | eq : Tm → Tm → Fm
  | neg : Fm → Fm
  | and : Fm → Fm → Fm
  | ex : ℕ → Fm → Fm
deriving DecidableEq

/-! ### Semantics in the standard model `ℕ` -/

/-- Value of a term under an assignment of naturals to variables. -/
def Tm.eval (v : ℕ → ℕ) : Tm → ℕ
  | .var n => v n
  | .num n => n
  | .add a b => a.eval v + b.eval v
  | .mul a b => a.eval v * b.eval v

/-- Satisfaction of a formula in the standard model `ℕ`, under an assignment. -/
def Fm.Sat : Fm → (ℕ → ℕ) → Prop
  | .eq a b, v => a.eval v = b.eval v
  | .neg f, v => ¬ f.Sat v
  | .and f g, v => f.Sat v ∧ g.Sat v
  | .ex n f, v => ∃ k, f.Sat (Function.update v n k)

@[simp] theorem Fm.Sat_eq (a b : Tm) (v) : (Fm.eq a b).Sat v ↔ a.eval v = b.eval v := Iff.rfl
@[simp] theorem Fm.Sat_neg (f : Fm) (v) : (Fm.neg f).Sat v ↔ ¬ f.Sat v := Iff.rfl
@[simp] theorem Fm.Sat_and (f g : Fm) (v) : (Fm.and f g).Sat v ↔ f.Sat v ∧ g.Sat v := Iff.rfl
@[simp] theorem Fm.Sat_ex (n : ℕ) (f : Fm) (v) :
    (Fm.ex n f).Sat v ↔ ∃ k, f.Sat (Function.update v n k) := Iff.rfl

/-! ### Free variables -/

/-- The variables occurring in a term. -/
def Tm.vars : Tm → Finset ℕ
  | .var n => {n}
  | .num _ => ∅
  | .add a b => a.vars ∪ b.vars
  | .mul a b => a.vars ∪ b.vars

/-- The free variables of a formula. -/
def Fm.freeVars : Fm → Finset ℕ
  | .eq a b => a.vars ∪ b.vars
  | .neg f => f.freeVars
  | .and f g => f.freeVars ∪ g.freeVars
  | .ex n f => f.freeVars.erase n

/-- A sentence is a formula without free variables. -/
def Fm.IsSentence (f : Fm) : Prop := f.freeVars = ∅

theorem Tm.eval_congr : ∀ (t : Tm) {v w : ℕ → ℕ}, (∀ n ∈ t.vars, v n = w n) →
    t.eval v = t.eval w
  | .var n, _, _, h => h n (by simp [Tm.vars])
  | .num _, _, _, _ => rfl
  | .add a b, v, w, h => by
      simp only [Tm.eval]
      rw [a.eval_congr (fun n hn => h n (by simp [Tm.vars, hn])),
        b.eval_congr (fun n hn => h n (by simp [Tm.vars, hn]))]
  | .mul a b, v, w, h => by
      simp only [Tm.eval]
      rw [a.eval_congr (fun n hn => h n (by simp [Tm.vars, hn])),
        b.eval_congr (fun n hn => h n (by simp [Tm.vars, hn]))]

/-- Satisfaction only depends on the values of the free variables. -/
theorem Fm.sat_congr : ∀ (f : Fm) {v w : ℕ → ℕ}, (∀ n ∈ f.freeVars, v n = w n) →
    (f.Sat v ↔ f.Sat w)
  | .eq a b, v, w, h => by
      simp only [Fm.Sat_eq]
      rw [a.eval_congr (fun n hn => h n (by simp [Fm.freeVars, hn])),
        b.eval_congr (fun n hn => h n (by simp [Fm.freeVars, hn]))]
  | .neg f, v, w, h => by
      simp only [Fm.Sat_neg]
      exact not_congr (f.sat_congr h)
  | .and f g, v, w, h => by
      simp only [Fm.Sat_and]
      exact and_congr (f.sat_congr (fun n hn => h n (by simp [Fm.freeVars, hn])))
        (g.sat_congr (fun n hn => h n (by simp [Fm.freeVars, hn])))
  | .ex m f, v, w, h => by
      simp only [Fm.Sat_ex]
      refine exists_congr (fun k => f.sat_congr (fun n hn => ?_))
      by_cases hnm : n = m
      · subst hnm; simp
      · rw [Function.update_of_ne hnm, Function.update_of_ne hnm]
        exact h n (by simp [Fm.freeVars, Finset.mem_erase, hnm, hn])

/-! ### Gödel numbering -/

/-- Gödel numbering of terms. -/
def Tm.enc : Tm → ℕ
  | .var n => 4 * n
  | .num n => 4 * n + 1
  | .add a b => 4 * pairP a.enc b.enc + 2
  | .mul a b => 4 * pairP a.enc b.enc + 3

/-- Gödel numbering of formulas. -/
def Fm.enc : Fm → ℕ
  | .eq a b => 4 * pairP a.enc b.enc
  | .neg f => 4 * f.enc + 1
  | .and f g => 4 * pairP f.enc g.enc + 2
  | .ex n f => 4 * pairP n f.enc + 3

theorem Tm.enc_injective : Function.Injective Tm.enc := by
  intro a
  induction a with
  | var n => intro b; cases b <;> simp [Tm.enc] <;> omega
  | num n => intro b; cases b <;> simp [Tm.enc] <;> omega
  | add p q ihp ihq =>
      intro b
      cases b with
      | var m => intro h; simp only [Tm.enc] at h; omega
      | num m => intro h; simp only [Tm.enc] at h; omega
      | add r s =>
          intro h; simp only [Tm.enc] at h
          have h' : pairP p.enc q.enc = pairP r.enc s.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [ihp h1, ihq h2]
      | mul r s => intro h; simp only [Tm.enc] at h; omega
  | mul p q ihp ihq =>
      intro b
      cases b with
      | var m => intro h; simp only [Tm.enc] at h; omega
      | num m => intro h; simp only [Tm.enc] at h; omega
      | add r s => intro h; simp only [Tm.enc] at h; omega
      | mul r s =>
          intro h; simp only [Tm.enc] at h
          have h' : pairP p.enc q.enc = pairP r.enc s.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [ihp h1, ihq h2]

theorem Fm.enc_injective : Function.Injective Fm.enc := by
  intro a
  induction a with
  | eq s t =>
      intro b
      cases b with
      | eq s' t' =>
          intro h; simp only [Fm.enc] at h
          have h' : pairP s.enc t.enc = pairP s'.enc t'.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [Tm.enc_injective h1, Tm.enc_injective h2]
      | neg g => intro h; simp only [Fm.enc] at h; omega
      | and g g' => intro h; simp only [Fm.enc] at h; omega
      | ex n g => intro h; simp only [Fm.enc] at h; omega
  | neg f ih =>
      intro b
      cases b with
      | eq s' t' => intro h; simp only [Fm.enc] at h; omega
      | neg g => intro h; simp only [Fm.enc] at h; exact congrArg Fm.neg (ih (by omega))
      | and g g' => intro h; simp only [Fm.enc] at h; omega
      | ex n g => intro h; simp only [Fm.enc] at h; omega
  | and f g ihf ihg =>
      intro b
      cases b with
      | eq s' t' => intro h; simp only [Fm.enc] at h; omega
      | neg g' => intro h; simp only [Fm.enc] at h; omega
      | and p q =>
          intro h; simp only [Fm.enc] at h
          have h' : pairP f.enc g.enc = pairP p.enc q.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [ihf h1, ihg h2]
      | ex n g' => intro h; simp only [Fm.enc] at h; omega
  | ex n f ih =>
      intro b
      cases b with
      | eq s' t' => intro h; simp only [Fm.enc] at h; omega
      | neg g' => intro h; simp only [Fm.enc] at h; omega
      | and p q => intro h; simp only [Fm.enc] at h; omega
      | ex m g =>
          intro h; simp only [Fm.enc] at h
          have h' : pairP n f.enc = pairP m g.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [h1, ih h2]

/-! ### Arithmetical truth and definability -/

/-- The set of Gödel numbers of true sentences of arithmetic (arithmetical truth). -/
def TruthSet : Set ℕ :=
  {n | ∃ φ : Fm, φ.IsSentence ∧ φ.enc = n ∧ φ.Sat (fun _ => 0)}

/-- A set of naturals is (arithmetically) definable if there is an arithmetical formula
whose only free variable is `x₀` and which holds, in the standard model, exactly of the
members of the set. -/
def Definable (S : Set ℕ) : Prop :=
  ∃ θ : Fm, θ.freeVars ⊆ {0} ∧
    ∀ n : ℕ, (θ.Sat (Function.update (fun _ => 0) 0 n) ↔ n ∈ S)

/-! ### The diagonalisation machinery -/

/-- `subFm φ c` is the formula `∃ x₀ (x₀ = c ∧ φ)`, i.e. `φ` with `x₀` set to `c`. -/
def subFm (φ : Fm) (c : ℕ) : Fm := .ex 0 (.and (.eq (.var 0) (.num c)) φ)

theorem sat_subFm (φ : Fm) (c : ℕ) (v : ℕ → ℕ) :
    (subFm φ c).Sat v ↔ φ.Sat (Function.update v 0 c) := by
  simp only [subFm, Fm.Sat_ex, Fm.Sat_and, Fm.Sat_eq, Tm.eval, Function.update_self]
  constructor
  · rintro ⟨k, hk, h⟩
    subst hk; exact h
  · intro h
    exact ⟨c, rfl, h⟩

theorem freeVars_subFm (φ : Fm) (c : ℕ) :
    (subFm φ c).freeVars = (φ.freeVars).erase 0 := by
  simp [subFm, Fm.freeVars, Tm.vars]

/-- The arithmetic function computing the Gödel number of `subFm φ c` from `c` and
the Gödel number of `φ`. -/
def encSub (c e : ℕ) : ℕ :=
  4 * pairP 0 (4 * pairP (4 * pairP 0 (4 * c + 1)) e + 2) + 3

theorem enc_subFm (φ : Fm) (c : ℕ) : (subFm φ c).enc = encSub c φ.enc := by
  simp [subFm, Fm.enc, Tm.enc, encSub]

/-- The diagonal function: `diagF c` is the Gödel number of `subFm φ c` when `c = φ.enc`. -/
def diagF (c : ℕ) : ℕ := encSub c c

/-! ### A term defining the diagonal function -/

private def tPair (s t : Tm) : Tm :=
  .add (.mul (.add s t) (.add (.add s t) (.num 1))) (.mul (.num 2) s)

private theorem eval_tPair (s t : Tm) (v : ℕ → ℕ) :
    (tPair s t).eval v = pairP (s.eval v) (t.eval v) := by
  simp [tPair, Tm.eval, pairP]

private theorem vars_tPair (s t : Tm) : (tPair s t).vars = s.vars ∪ t.vars := by
  ext x; simp [tPair, Tm.vars]; tauto

/-- A term in the single variable `x₀` whose value is `diagF x₀`. -/
def tDiag : Tm :=
  .add (.mul (.num 4)
    (tPair (.num 0)
      (.add (.mul (.num 4)
        (tPair (.mul (.num 4) (tPair (.num 0) (.add (.mul (.num 4) (.var 0)) (.num 1))))
          (.var 0))) (.num 2)))) (.num 3)

theorem eval_tDiag (v : ℕ → ℕ) : tDiag.eval v = diagF (v 0) := by
  simp [tDiag, diagF, encSub, eval_tPair, Tm.eval]

theorem vars_tDiag : tDiag.vars = {0} := by
  ext x
  simp [tDiag, vars_tPair, Tm.vars]

/-- The formula `x₁ = diagF x₀`. -/
def deltaFm : Fm := .eq (.var 1) tDiag

theorem sat_deltaFm (v : ℕ → ℕ) : deltaFm.Sat v ↔ v 1 = diagF (v 0) := by
  simp [deltaFm, Tm.eval, eval_tDiag]

theorem freeVars_deltaFm : deltaFm.freeVars = {0, 1} := by
  ext x
  simp [deltaFm, Fm.freeVars, Tm.vars, vars_tDiag]
  tauto

/-! ### Tarski's undefinability theorem -/

/-- Given a candidate truth-definition `θ`, the diagonal formula
`¬ ∃ x₁ (x₁ = diagF x₀ ∧ θ(x₁))`. -/
def diagOf (θ : Fm) : Fm :=
  .neg (.ex 1 (.and deltaFm (.ex 0 (.and (.eq (.var 0) (.var 1)) θ))))

theorem freeVars_diagOf {θ : Fm} (hθ : θ.freeVars ⊆ {0}) :
    (diagOf θ).freeVars ⊆ {0} := by
  intro x hx
  simp only [diagOf, Fm.freeVars, freeVars_deltaFm, Finset.mem_erase, Finset.mem_union,
    Tm.vars] at hx
  simp only [Finset.mem_singleton]
  rcases hx with ⟨hx1, hx2⟩
  rcases hx2 with hx2 | hx2
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    omega
  · rcases hx2 with ⟨hx0, hx2⟩
    rcases hx2 with hx2 | hx2
    · simp only [Finset.mem_singleton] at hx2
      omega
    · have := hθ hx2
      simpa using this

theorem sat_diagOf {θ : Fm} (v : ℕ → ℕ) :
    (diagOf θ).Sat v ↔
      ¬ θ.Sat (Function.update (Function.update v 1 (diagF (v 0))) 0 (diagF (v 0))) := by
  simp only [diagOf, Fm.Sat_neg, Fm.Sat_ex, Fm.Sat_and, not_exists]
  constructor
  · intro h hsat
    refine h (diagF (v 0)) ⟨?_, diagF (v 0), ?_, hsat⟩
    · rw [sat_deltaFm]
      simp
    · simp [Tm.eval]
  · intro h k hk
    obtain ⟨hd, m, hm, hsat⟩ := hk
    rw [sat_deltaFm] at hd
    simp only [Function.update_self,
      Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega)] at hd
    simp only [Fm.Sat_eq, Tm.eval, Function.update_self,
      Function.update_of_ne (show (1 : ℕ) ≠ 0 by omega)] at hm
    subst hm
    subst hd
    exact h hsat

/-- **Tarski's undefinability theorem.**  Arithmetical truth — the set of Gödel numbers
of true sentences of arithmetic — is not arithmetically definable. -/
theorem Tarski_undefinability : ¬ Definable TruthSet := by
  rintro ⟨θ, hθfree, hθ⟩
  set ψ : Fm := diagOf θ with hψ
  have hψfree : ψ.freeVars ⊆ {0} := freeVars_diagOf hθfree
  set c : ℕ := ψ.enc with hc
  set σ : Fm := subFm ψ c with hσ
  -- `σ` is a sentence
  have hσsent : σ.IsSentence := by
    rw [Fm.IsSentence, hσ, freeVars_subFm]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_erase] at hx
    have := hψfree hx.2
    simp only [Finset.mem_singleton] at this
    exact hx.1 this
  -- the Gödel number of `σ` is `diagF c`
  have hσenc : σ.enc = diagF c := by rw [hσ, enc_subFm, diagF]
  -- membership of `diagF c` in the truth set is equivalent to the truth of `σ`
  have hmem : diagF c ∈ TruthSet ↔ σ.Sat (fun _ => 0) := by
    constructor
    · rintro ⟨φ, _, hφenc, hφsat⟩
      have : φ = σ := Fm.enc_injective (by rw [hφenc, hσenc])
      rwa [this] at hφsat
    · intro h
      exact ⟨σ, hσsent, hσenc, h⟩
  -- unfold the truth of `σ`
  have h1 : σ.Sat (fun _ => 0) ↔ ψ.Sat (Function.update (fun _ => 0) 0 c) := by
    rw [hσ, sat_subFm]
  have hv0 : (Function.update (fun _ : ℕ => (0:ℕ)) 0 c) 0 = c := by simp
  have h2 : ψ.Sat (Function.update (fun _ => 0) 0 c) ↔
      ¬ θ.Sat (Function.update (Function.update (Function.update (fun _ : ℕ => (0:ℕ)) 0 c) 1
        (diagF c)) 0 (diagF c)) := by
    rw [hψ, sat_diagOf, hv0]
  -- the two assignments agree on the free variables of `θ`
  have h3 : θ.Sat (Function.update (Function.update (Function.update (fun _ : ℕ => (0:ℕ)) 0 c) 1
        (diagF c)) 0 (diagF c)) ↔
      θ.Sat (Function.update (fun _ : ℕ => (0:ℕ)) 0 (diagF c)) := by
    refine Fm.sat_congr θ (fun n hn => ?_)
    have hn0 : n = 0 := by simpa using hθfree hn
    subst hn0
    simp
  rw [h1, h2, h3, hθ (diagF c)] at hmem
  tauto

/-! ### Sanity checks

These confirm that the notions above are not vacuous: some sets *are* definable, and the
truth set is a genuine, nonempty proper subset of the set of Gödel numbers. -/

/-- The set of even numbers is arithmetically definable. -/
theorem definable_even : Definable {n : ℕ | ∃ k, n = 2 * k} := by
  refine ⟨.ex 1 (.eq (.var 0) (.mul (.num 2) (.var 1))), ?_, ?_⟩
  · intro x hx
    simp only [Fm.freeVars, Finset.mem_erase, Tm.vars, Finset.mem_union,
      Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hx1, hx2 | hx2⟩
    · exact hx2
    · simp only [Finset.notMem_empty, false_or] at hx2
      omega
  · intro n
    simp only [Fm.Sat_ex, Fm.Sat_eq, Tm.eval, Function.update_self,
      Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega), Set.mem_setOf_eq]

/-- The truth set is nonempty: the true sentence `0 = 0` belongs to it. -/
theorem zero_eq_zero_mem_TruthSet : (Fm.eq (.num 0) (.num 0)).enc ∈ TruthSet :=
  ⟨_, by simp [Fm.IsSentence, Fm.freeVars, Tm.vars], rfl, rfl⟩

/-- A false sentence is not in the truth set. -/
theorem zero_eq_one_notMem_TruthSet : (Fm.eq (.num 0) (.num 1)).enc ∉ TruthSet := by
  rintro ⟨φ, -, hφ, hsat⟩
  have h : φ = Fm.eq (.num 0) (.num 1) := Fm.enc_injective hφ
  subst h
  simp [Fm.Sat, Tm.eval] at hsat

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

