import RequestProject.Loeb

/-!
# Soundness and consistency of the calculus

We interpret the language of arithmetic in the standard model `ℕ` and prove that every formula
provable in `Frontier.Provable` is true in `ℕ` under every assignment.  In particular the
calculus is consistent (`Frontier.Provable_consistent`), so the formalization of Peano
Arithmetic used for Löb's theorem is not degenerate.
-/

namespace Frontier

/-! ## The standard model -/

/-- Extend an assignment by a value for the variable bound by the outermost `∀`. -/
def push (n : ℕ) (env : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => env i

/-- The assignment corresponding to inserting the value `v` at index `k`, shifting the
assignments of the indices `≥ k` upwards. -/
def insertAt (k v : ℕ) (env : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i < k then env i else if i = k then v else env (i - 1)

/-- The assignment obtained by changing the value at index `k` to `v`. -/
def updateAt (k v : ℕ) (env : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i = k then v else env i

/-- Value of a term in the standard model `ℕ` under an assignment to the variables. -/
def Trm.eval : Trm → (ℕ → ℕ) → ℕ
  | .var n, env => env n
  | .zero, _ => 0
  | .succ t, env => t.eval env + 1
  | .add t u, env => t.eval env + u.eval env
  | .mul t u, env => t.eval env * u.eval env

/-- Truth of a formula in the standard model `ℕ` under an assignment to the variables. -/
def Fml.Sat : Fml → (ℕ → ℕ) → Prop
  | .eq t u, env => t.eval env = u.eval env
  | .bot, _ => False
  | .imp a b, env => a.Sat env → b.Sat env
  | .all a, env => ∀ n, a.Sat (push n env)

/-! ## Assignment bookkeeping -/

theorem insertAt_zero (v : ℕ) (env : ℕ → ℕ) : insertAt 0 v env = push v env := by
  funext i
  cases i <;> simp [insertAt, push]

theorem insertAt_succ (k v n : ℕ) (env : ℕ → ℕ) :
    insertAt (k + 1) v (push n env) = push n (insertAt k v env) := by
  funext i
  match i with
  | 0 => simp [insertAt, push]
  | i + 1 =>
    by_cases h1 : i < k
    · simp [insertAt, push, h1, Nat.succ_lt_succ h1]
    · by_cases h2 : i = k
      · subst h2; simp [insertAt, push]
      · have h3 : k < i := by omega
        have h4 : i ≠ 0 := by omega
        match i with
        | 0 => omega
        | i + 1 => simp [insertAt, push]

theorem updateAt_succ (k v n : ℕ) (env : ℕ → ℕ) :
    updateAt (k + 1) v (push n env) = push n (updateAt k v env) := by
  funext i
  cases i <;> simp [updateAt, push]

theorem updateAt_zero_push (v n : ℕ) (env : ℕ → ℕ) :
    updateAt 0 v (push n env) = push v env := by
  funext i
  cases i <;> simp [updateAt, push]

/-! ## The substitution lemmas -/

theorem Trm.eval_lift (t : Trm) (c v : ℕ) (env : ℕ → ℕ) :
    (t.lift c).eval (insertAt c v env) = t.eval env := by
  induction t with
  | var n =>
    by_cases h : n < c
    · simp [Trm.lift, Trm.eval, insertAt, h]
    · have : ¬ (n + 1 < c) := by omega
      have : n + 1 ≠ c := by omega
      simp [Trm.lift, Trm.eval, insertAt, h, this]
      omega
  | zero => rfl
  | succ t ih => simp [Trm.lift, Trm.eval, ih]
  | add t u iht ihu => simp [Trm.lift, Trm.eval, iht, ihu]
  | mul t u iht ihu => simp [Trm.lift, Trm.eval, iht, ihu]

theorem Trm.eval_subst (t : Trm) (k : ℕ) (s : Trm) (env : ℕ → ℕ) :
    (t.subst k s).eval env = t.eval (insertAt k (s.eval env) env) := by
  induction t with
  | var n =>
    by_cases h1 : n = k
    · simp [Trm.subst, Trm.eval, insertAt, h1]
    · by_cases h2 : k < n
      · have : ¬ (n < k) := by omega
        simp [Trm.subst, Trm.eval, insertAt, h1, h2, this]
      · have h3 : n < k := by omega
        simp [Trm.subst, Trm.eval, insertAt, h1, h2, h3]
  | zero => rfl
  | succ t ih => simp [Trm.subst, Trm.eval, ih]
  | add t u iht ihu => simp [Trm.subst, Trm.eval, iht, ihu]
  | mul t u iht ihu => simp [Trm.subst, Trm.eval, iht, ihu]

theorem Trm.eval_substK (t : Trm) (k : ℕ) (s : Trm) (env : ℕ → ℕ) :
    (t.substK k s).eval env = t.eval (updateAt k (s.eval env) env) := by
  induction t with
  | var n => by_cases h1 : n = k <;> simp [Trm.substK, Trm.eval, updateAt, h1]
  | zero => rfl
  | succ t ih => simp [Trm.substK, Trm.eval, ih]
  | add t u iht ihu => simp [Trm.substK, Trm.eval, iht, ihu]
  | mul t u iht ihu => simp [Trm.substK, Trm.eval, iht, ihu]

theorem Fml.sat_subst (φ : Fml) (k : ℕ) (s : Trm) (env : ℕ → ℕ) :
    (φ.subst k s).Sat env ↔ φ.Sat (insertAt k (s.eval env) env) := by
  induction φ generalizing k s env with
  | eq t u => simp [Fml.subst, Fml.Sat, Trm.eval_subst]
  | bot => simp [Fml.subst, Fml.Sat]
  | imp a b iha ihb => simp [Fml.subst, Fml.Sat, iha, ihb]
  | all a ih =>
    simp only [Fml.subst, Fml.Sat, ih]
    have key : ∀ n : ℕ, insertAt (k + 1) ((s.lift 0).eval (push n env)) (push n env)
        = push n (insertAt k (s.eval env) env) := by
      intro n
      have hs : (s.lift 0).eval (push n env) = s.eval env := by
        rw [← insertAt_zero n env]; exact Trm.eval_lift s 0 n env
      rw [hs, insertAt_succ]
    constructor
    · intro h n; rw [← key n]; exact h n
    · intro h n; rw [key n]; exact h n

theorem Fml.sat_substK (φ : Fml) (k : ℕ) (s : Trm) (env : ℕ → ℕ) :
    (φ.substK k s).Sat env ↔ φ.Sat (updateAt k (s.eval env) env) := by
  induction φ generalizing k s env with
  | eq t u => simp [Fml.substK, Fml.Sat, Trm.eval_substK]
  | bot => simp [Fml.substK, Fml.Sat]
  | imp a b iha ihb => simp [Fml.substK, Fml.Sat, iha, ihb]
  | all a ih =>
    simp only [Fml.substK, Fml.Sat, ih]
    have key : ∀ n : ℕ, updateAt (k + 1) ((s.lift 0).eval (push n env)) (push n env)
        = push n (updateAt k (s.eval env) env) := by
      intro n
      have hs : (s.lift 0).eval (push n env) = s.eval env := by
        rw [← insertAt_zero n env]; exact Trm.eval_lift s 0 n env
      rw [hs, updateAt_succ]
    constructor
    · intro h n; rw [← key n]; exact h n
    · intro h n; rw [key n]; exact h n

theorem Fml.sat_inst (φ : Fml) (t : Trm) (env : ℕ → ℕ) :
    (φ.inst t).Sat env ↔ φ.Sat (push (t.eval env) env) := by
  rw [Fml.inst, Fml.sat_subst, insertAt_zero]

/-! ## Soundness -/

open Classical in
theorem propEval_eq_decide (env : ℕ → ℕ) (φ : Fml) :
    propEval (fun ψ => decide (ψ.Sat env)) φ = decide (φ.Sat env) := by
  induction φ with
  | eq t u => rfl
  | bot => simp [propEval, Fml.Sat]
  | imp a b iha ihb =>
    simp only [propEval, iha, ihb, Fml.Sat]
    by_cases ha : a.Sat env <;> by_cases hb : b.Sat env <;> simp [ha, hb]
  | all a => rfl

open Classical in
theorem Tautology.sat {φ : Fml} (h : Tautology φ) (env : ℕ → ℕ) : φ.Sat env := by
  have := h (fun ψ => decide (ψ.Sat env))
  rw [propEval_eq_decide] at this
  exact of_decide_eq_true this

theorem LogicalAxiom.sat {φ : Fml} (h : LogicalAxiom φ) (env : ℕ → ℕ) : φ.Sat env := by
  induction h with
  | taut h => exact h.sat env
  | allElim φ t =>
    intro h
    rw [Fml.sat_inst]
    exact h _
  | allImp φ ψ => exact fun h hφ n => h n (hφ n)
  | eqRefl => intro n; rfl
  | eqSucc => intro n m h; simp [Fml.Sat, Trm.eval, push] at h ⊢; omega
  | eqAdd => intro a b c d; simp [Fml.Sat, Trm.eval, push]; omega
  | eqMul =>
    intro a b c d
    simp only [Fml.Sat, Trm.eval, push]
    intro h1 h2
    subst h1; subst h2; rfl
  | eqCongr => intro a b c d; simp [Fml.Sat, Trm.eval, push]; omega

theorem PAAxiom.sat {φ : Fml} (h : PAAxiom φ) (env : ℕ → ℕ) : φ.Sat env := by
  induction h with
  | succNeZero => intro n; simp [Fml.neg, Fml.Sat, Trm.eval, push]
  | succInj => intro n m; simp [Fml.Sat, Trm.eval, push]
  | addZero => intro n; simp [Fml.Sat, Trm.eval, push]
  | addSucc => intro n m; simp [Fml.Sat, Trm.eval, push]; omega
  | mulZero => intro n; simp [Fml.Sat, Trm.eval, push]
  | mulSucc => intro n m; simp [Fml.Sat, Trm.eval, push, Nat.mul_succ]
  | induction φ =>
    intro h0 hstep n
    induction n with
    | zero =>
      rw [Fml.sat_inst] at h0
      exact h0
    | succ n ih =>
      have hthis := hstep n ih
      rw [Fml.sat_substK] at hthis
      have heval : (Trm.succ (Trm.var 0)).eval (push n env) = n + 1 := rfl
      rw [heval, updateAt_zero_push] at hthis
      exact hthis

/-- **Soundness**: everything provable in the calculus is true in the standard model `ℕ`. -/
theorem soundness {φ : Fml} (h : ⊢ φ) : ∀ env : ℕ → ℕ, φ.Sat env := by
  induction h with
  | logic h => exact h.sat
  | ax h => exact h.sat
  | mp _ _ ih₁ ih₂ => exact fun env => ih₁ env (ih₂ env)
  | gen _ ih => exact fun env n => ih (push n env)

/-- The calculus is consistent: `⊥` is not provable. -/
theorem Provable_consistent : ¬ (⊢ Fml.bot) := fun h => soundness h (fun _ => 0)

end Frontier

import Mathlib

/-!
# Löb's theorem for Peano Arithmetic

This file contains a self-contained formalization of the syntax of first-order arithmetic,
of a Hilbert-style proof calculus for Peano Arithmetic (`Frontier.Provable`), and a proof of
**Löb's theorem**: if `PA ⊢ □φ → φ` then `PA ⊢ φ`, where `□` is any operation on formulas
satisfying the Hilbert–Bernays–Löb derivability conditions together with the Gödel diagonal
(fixed point) property.  The intended instance of `□` is `fun φ => Prov(⌜φ⌝)`, the arithmetized
provability predicate of `PA` applied to the numeral of the Gödel number of `φ`; the derivability
conditions and the diagonal lemma for that particular `□` are the standard arithmetization
facts and are taken here as explicit hypotheses of the theorem (they are *not* axioms: the
theorem is a plain implication, and `Frontier.derivability_conditions_satisfiable` exhibits a
concrete `□` satisfying all of them, so the statement is not vacuous).
-/

namespace Frontier

/-! ## Syntax -/

/-- Terms of the language of arithmetic `{0, S, +, *}`, with de Bruijn indexed variables. -/
inductive Trm where
  | var : ℕ → Trm
  | zero : Trm
  | succ : Trm → Trm
  | add : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  deriving DecidableEq

/-- Formulas of the language of arithmetic, with de Bruijn indexed variables.
`⊥` and `→` are primitive; the other connectives are defined below. -/
inductive Fml where
  | eq : Trm → Trm → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | all : Fml → Fml
  deriving DecidableEq

/-- Implication of formulas. -/
infixr:55 " ⟹ " => Fml.imp

/-- Negation, `¬φ := φ → ⊥`. -/
def Fml.neg (φ : Fml) : Fml := φ ⟹ Fml.bot

/-- Conjunction, `φ ∧ ψ := ¬(φ → ¬ψ)`. -/
def Fml.and (φ ψ : Fml) : Fml := (φ ⟹ ψ.neg).neg

/-- Biconditional, `φ ↔ ψ := (φ → ψ) ∧ (ψ → φ)`. -/
def Fml.iff (φ ψ : Fml) : Fml := (φ ⟹ ψ).and (ψ ⟹ φ)

/-- Biconditional of formulas. -/
infix:50 " ⇔ " => Fml.iff

/-- The numeral of `n`, i.e. `S (S (... S 0))`. -/
def numeral : ℕ → Trm
  | 0 => Trm.zero
  | n + 1 => Trm.succ (numeral n)

/-! ### Lifting and substitution (de Bruijn) -/

/-- Increment all variables with index `≥ c`. -/
def Trm.lift : Trm → ℕ → Trm
  | .var n, c => .var (if n < c then n else n + 1)
  | .zero, _ => .zero
  | .succ t, c => .succ (t.lift c)
  | .add t u, c => .add (t.lift c) (u.lift c)
  | .mul t u, c => .mul (t.lift c) (u.lift c)

/-- Substitute the term `s` for the variable `k`, decrementing the higher variables. -/
def Trm.subst : Trm → ℕ → Trm → Trm
  | .var n, k, s => if n = k then s else if k < n then .var (n - 1) else .var n
  | .zero, _, _ => .zero
  | .succ t, k, s => .succ (t.subst k s)
  | .add t u, k, s => .add (t.subst k s) (u.subst k s)
  | .mul t u, k, s => .mul (t.subst k s) (u.subst k s)

/-- Substitute the term `s` for the variable `k` in a formula. -/
def Fml.subst : Fml → ℕ → Trm → Fml
  | .eq t u, k, s => .eq (t.subst k s) (u.subst k s)
  | .bot, _, _ => .bot
  | .imp a b, k, s => .imp (a.subst k s) (b.subst k s)
  | .all a, k, s => .all (a.subst (k + 1) (s.lift 0))

/-- Substitute the term `s` for the variable `k`, *without* renaming the other variables.
This is the operation used to state the induction scheme. -/
def Trm.substK : Trm → ℕ → Trm → Trm
  | .var n, k, s => if n = k then s else .var n
  | .zero, _, _ => .zero
  | .succ t, k, s => .succ (t.substK k s)
  | .add t u, k, s => .add (t.substK k s) (u.substK k s)
  | .mul t u, k, s => .mul (t.substK k s) (u.substK k s)

/-- Substitute the term `s` for the variable `k` in a formula, without renaming the other
variables. -/
def Fml.substK : Fml → ℕ → Trm → Fml
  | .eq t u, k, s => .eq (t.substK k s) (u.substK k s)
  | .bot, _, _ => .bot
  | .imp a b, k, s => .imp (a.substK k s) (b.substK k s)
  | .all a, k, s => .all (a.substK (k + 1) (s.lift 0))

/-- Instantiate the variable bound by an outermost `∀` with the term `t`. -/
def Fml.inst (φ : Fml) (t : Trm) : Fml := φ.subst 0 t

/-! ## Propositional tautologies -/

/-- Evaluation of a formula under a boolean assignment `v` to the *prime* formulas
(atomic formulas and universally quantified formulas), treating `⊥` and `→` as the
classical boolean connectives. -/
def propEval (v : Fml → Bool) : Fml → Bool
  | .eq t u => v (.eq t u)
  | .bot => false
  | .imp a b => !(propEval v a) || propEval v b
  | .all a => v (.all a)

/-- A formula is a (propositional) tautology if it evaluates to `true` under every boolean
assignment to its prime subformulas.  Equivalently, it is a substitution instance of a
tautology of propositional logic. -/
def Tautology (φ : Fml) : Prop := ∀ v : Fml → Bool, propEval v φ = true

/-! ## The proof calculus -/

/-- The logical axioms: all tautologies, the equality axioms, and the two quantifier axioms.
(Generalization is a rule of the calculus, see `Frontier.Provable`.) -/
inductive LogicalAxiom : Fml → Prop
  /-- Every propositional tautology (in the language of arithmetic) is an axiom. -/
  | taut {φ : Fml} : Tautology φ → LogicalAxiom φ
  /-- `∀x φ → φ[t/x]`. -/
  | allElim (φ : Fml) (t : Trm) : LogicalAxiom ((Fml.all φ) ⟹ φ.inst t)
  /-- `∀x (φ → ψ) → (∀x φ → ∀x ψ)`. -/
  | allImp (φ ψ : Fml) :
      LogicalAxiom ((Fml.all (φ ⟹ ψ)) ⟹ ((Fml.all φ) ⟹ (Fml.all ψ)))
  /-- `∀x (x = x)`. -/
  | eqRefl : LogicalAxiom (Fml.all (.eq (.var 0) (.var 0)))
  /-- `∀x ∀y (x = y → S x = S y)`. -/
  | eqSucc : LogicalAxiom
      (Fml.all (Fml.all (Fml.eq (.var 1) (.var 0) ⟹
        Fml.eq (.succ (.var 1)) (.succ (.var 0)))))
  /-- `∀x ∀y ∀z ∀w (x = y → (z = w → x + z = y + w))`. -/
  | eqAdd : LogicalAxiom
      (Fml.all (Fml.all (Fml.all (Fml.all
        (Fml.eq (.var 3) (.var 2) ⟹ Fml.eq (.var 1) (.var 0) ⟹
          Fml.eq (.add (.var 3) (.var 1)) (.add (.var 2) (.var 0)))))))
  /-- `∀x ∀y ∀z ∀w (x = y → (z = w → x * z = y * w))`. -/
  | eqMul : LogicalAxiom
      (Fml.all (Fml.all (Fml.all (Fml.all
        (Fml.eq (.var 3) (.var 2) ⟹ Fml.eq (.var 1) (.var 0) ⟹
          Fml.eq (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 0)))))))
  /-- `∀x ∀y ∀z ∀w (x = y → (z = w → (x = z → y = w)))`. -/
  | eqCongr : LogicalAxiom
      (Fml.all (Fml.all (Fml.all (Fml.all
        (Fml.eq (.var 3) (.var 2) ⟹ Fml.eq (.var 1) (.var 0) ⟹
          Fml.eq (.var 3) (.var 1) ⟹ Fml.eq (.var 2) (.var 0))))))

/-- The non-logical axioms of Peano Arithmetic. -/
inductive PAAxiom : Fml → Prop
  /-- `∀x (S x ≠ 0)`. -/
  | succNeZero : PAAxiom (Fml.all (Fml.eq (.succ (.var 0)) .zero).neg)
  /-- `∀x ∀y (S x = S y → x = y)`. -/
  | succInj : PAAxiom
      (Fml.all (Fml.all (Fml.eq (.succ (.var 1)) (.succ (.var 0)) ⟹
        Fml.eq (.var 1) (.var 0))))
  /-- `∀x (x + 0 = x)`. -/
  | addZero : PAAxiom (Fml.all (Fml.eq (.add (.var 0) .zero) (.var 0)))
  /-- `∀x ∀y (x + S y = S (x + y))`. -/
  | addSucc : PAAxiom
      (Fml.all (Fml.all (Fml.eq (.add (.var 1) (.succ (.var 0)))
        (.succ (.add (.var 1) (.var 0))))))
  /-- `∀x (x * 0 = 0)`. -/
  | mulZero : PAAxiom (Fml.all (Fml.eq (.mul (.var 0) .zero) .zero))
  /-- `∀x ∀y (x * S y = x * y + x)`. -/
  | mulSucc : PAAxiom
      (Fml.all (Fml.all (Fml.eq (.mul (.var 1) (.succ (.var 0)))
        (.add (.mul (.var 1) (.var 0)) (.var 1)))))
  /-- The induction scheme:
  `φ[0/x] → (∀x (φ → φ[S x/x]) → ∀x φ)`, for every formula `φ`. -/
  | induction (φ : Fml) : PAAxiom
      (φ.inst .zero ⟹
        (Fml.all (φ ⟹ (φ.substK 0 (.succ (.var 0))))) ⟹ Fml.all φ)

/-- Provability in Peano Arithmetic: a Hilbert-style calculus with modus ponens and
generalization as rules. -/
inductive Provable : Fml → Prop
  | logic {φ : Fml} : LogicalAxiom φ → Provable φ
  | ax {φ : Fml} : PAAxiom φ → Provable φ
  | mp {φ ψ : Fml} : Provable (φ ⟹ ψ) → Provable φ → Provable ψ
  | gen {φ : Fml} : Provable φ → Provable (Fml.all φ)

/-- `⊢ φ` means that `φ` is provable in Peano Arithmetic. -/
notation "⊢ " φ => Provable φ

/-! ## Propositional reasoning inside the calculus -/

theorem Provable.taut {φ : Fml} (h : Tautology φ) : ⊢ φ := .logic (.taut h)

theorem imp_trans {a b c : Fml} (h₁ : ⊢ a ⟹ b) (h₂ : ⊢ b ⟹ c) : ⊢ a ⟹ c :=
  .mp (.mp (.taut (by
    intro v
    simp only [propEval]
    cases propEval v a <;> cases propEval v b <;> cases propEval v c <;> rfl)) h₁) h₂

theorem imp_distrib {a b c : Fml} (h₁ : ⊢ a ⟹ (b ⟹ c)) (h₂ : ⊢ a ⟹ b) : ⊢ a ⟹ c :=
  .mp (.mp (.taut (by
    intro v
    simp only [propEval]
    cases propEval v a <;> cases propEval v b <;> cases propEval v c <;> rfl)) h₁) h₂

theorem iff_mp {a b : Fml} (h : ⊢ a ⇔ b) : ⊢ a ⟹ b :=
  .mp (.taut (by
    intro v
    simp only [Fml.iff, Fml.and, Fml.neg, propEval]
    cases propEval v a <;> cases propEval v b <;> rfl)) h

theorem iff_mpr {a b : Fml} (h : ⊢ a ⇔ b) : ⊢ b ⟹ a :=
  .mp (.taut (by
    intro v
    simp only [Fml.iff, Fml.and, Fml.neg, propEval]
    cases propEval v a <;> cases propEval v b <;> rfl)) h

/-! ## The derivability conditions -/

/-- The Hilbert–Bernays–Löb derivability conditions for an operation `box` on formulas,
together with the Gödel fixed point (diagonal) property.  The intended instance is
`box φ = Prov(⌜φ⌝)`, the arithmetized provability predicate of `PA`. -/
structure DerivabilityConditions (box : Fml → Fml) : Prop where
  /-- D1 (necessitation): if `PA ⊢ φ` then `PA ⊢ □φ`. -/
  D1 : ∀ φ : Fml, (⊢ φ) → ⊢ box φ
  /-- D2 (distribution): `PA ⊢ □(φ → ψ) → (□φ → □ψ)`. -/
  D2 : ∀ φ ψ : Fml, ⊢ box (φ ⟹ ψ) ⟹ (box φ ⟹ box ψ)
  /-- D3 (provable necessitation): `PA ⊢ □φ → □□φ`. -/
  D3 : ∀ φ : Fml, ⊢ box φ ⟹ box (box φ)
  /-- The diagonal lemma, for the formulas needed in Löb's argument: for every `φ` there is a
  sentence `σ` with `PA ⊢ σ ↔ (□σ → φ)`. -/
  diagonal : ∀ φ : Fml, ∃ σ : Fml, ⊢ σ ⇔ (box σ ⟹ φ)

/-! ## Löb's theorem -/

/-- **Löb's theorem.**  Let `□` be the arithmetized provability predicate of Peano Arithmetic
(more generally, any operation on formulas satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma).  If `PA ⊢ □φ → φ`, then `PA ⊢ φ`. -/
theorem Loeb_theorem {box : Fml → Fml} (hbox : DerivabilityConditions box) (φ : Fml)
    (h : ⊢ box φ ⟹ φ) : ⊢ φ := by
  obtain ⟨σ, hσ⟩ := hbox.diagonal φ
  -- `⊢ σ → (□σ → φ)`
  have h1 : ⊢ σ ⟹ (box σ ⟹ φ) := iff_mp hσ
  -- `⊢ □σ → □(□σ → φ)`
  have h3 : ⊢ box σ ⟹ box (box σ ⟹ φ) := .mp (hbox.D2 σ (box σ ⟹ φ)) (hbox.D1 _ h1)
  -- `⊢ □σ → (□□σ → □φ)`
  have h5 : ⊢ box σ ⟹ (box (box σ) ⟹ box φ) :=
    imp_trans h3 (hbox.D2 (box σ) φ)
  -- `⊢ □σ → □φ`
  have h7 : ⊢ box σ ⟹ box φ := imp_distrib h5 (hbox.D3 σ)
  -- `⊢ □σ → φ`
  have h8 : ⊢ box σ ⟹ φ := imp_trans h7 h
  -- `⊢ σ`
  have h10 : ⊢ σ := .mp (iff_mpr hσ) h8
  -- `⊢ □σ`, hence `⊢ φ`
  exact .mp h8 (hbox.D1 σ h10)

/-! ## Non-vacuity -/

/-- The hypotheses of Löb's theorem are satisfiable: the operation `box φ = (0 = 0)` satisfies
all four conditions.  (Of course the intended instance is the arithmetized provability
predicate; this only records that `Frontier.Loeb_theorem` is not vacuously true.) -/
theorem derivability_conditions_satisfiable :
    DerivabilityConditions (fun _ => Fml.eq .zero .zero) := by
  have hzz : ⊢ Fml.eq Trm.zero Trm.zero := by
    have hax : ⊢ (Fml.eq (Trm.var 0) (Trm.var 0)).all ⟹
        (Fml.eq (Trm.var 0) (Trm.var 0)).inst Trm.zero :=
      .logic (.allElim (Fml.eq (.var 0) (.var 0)) .zero)
    have hinst : (Fml.eq (Trm.var 0) (Trm.var 0)).inst Trm.zero = Fml.eq Trm.zero Trm.zero := by
      decide
    rw [hinst] at hax
    exact .mp hax (.logic .eqRefl)
  refine ⟨fun _ _ => hzz, ?_, ?_, ?_⟩
  · intro φ ψ
    exact .taut (by
      intro v
      simp only [propEval]
      cases hv : v (Fml.eq Trm.zero Trm.zero) <;> simp)
  · intro φ
    exact .taut (by
      intro v
      simp only [propEval]
      cases hv : v (Fml.eq Trm.zero Trm.zero) <;> simp)
  · intro φ
    refine ⟨Fml.eq .zero .zero ⟹ φ, .taut ?_⟩
    intro v
    simp only [Fml.iff, Fml.and, Fml.neg, propEval]
    cases hv : v (Fml.eq Trm.zero Trm.zero) <;> cases hφ : propEval v φ <;> simp

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

