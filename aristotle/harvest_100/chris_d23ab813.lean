import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## Syntax of the language of arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, ·}`, with variables indexed
by natural numbers. -/
inductive Trm : Type
  | var : ℕ → Trm
  | zero : Trm
  | succ : Trm → Trm
  | add : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  deriving DecidableEq

/-- Formulas of the language of arithmetic: atomic equations, negation,
conjunction and universal quantification over a variable. -/
inductive Fml : Type
  | eq : Trm → Trm → Fml
  | not : Fml → Fml
  | and : Fml → Fml → Fml
  | all : ℕ → Fml → Fml
  deriving DecidableEq

/-- Implication, as an abbreviation. -/
def Fml.imp (p q : Fml) : Fml := Fml.not (Fml.and p (Fml.not q))

/-- Existential quantification, as an abbreviation. -/
def Fml.ex (i : ℕ) (p : Fml) : Fml := Fml.not (Fml.all i (Fml.not p))

/-! ## Semantics: the standard model `ℕ` -/

/-- Evaluation of a term in the standard model `ℕ` under an assignment of values
to the variables. -/
def Trm.eval : Trm → (ℕ → ℕ) → ℕ
  | Trm.var i, v => v i
  | Trm.zero, _ => 0
  | Trm.succ t, v => (t.eval v) + 1
  | Trm.add t u, v => t.eval v + u.eval v
  | Trm.mul t u, v => t.eval v * u.eval v

/-- Satisfaction (Tarskian truth) of a formula in the standard model `ℕ`
under an assignment of values to the variables. -/
def Fml.Sat : Fml → (ℕ → ℕ) → Prop
  | Fml.eq t u, v => t.eval v = u.eval v
  | Fml.not p, v => ¬ p.Sat v
  | Fml.and p q, v => p.Sat v ∧ q.Sat v
  | Fml.all i p, v => ∀ m : ℕ, p.Sat (Function.update v i m)

@[simp] theorem Fml.Sat_eq (t u : Trm) (v : ℕ → ℕ) :
    (Fml.eq t u).Sat v ↔ t.eval v = u.eval v := Iff.rfl

@[simp] theorem Fml.Sat_not (p : Fml) (v : ℕ → ℕ) :
    (Fml.not p).Sat v ↔ ¬ p.Sat v := Iff.rfl

@[simp] theorem Fml.Sat_and (p q : Fml) (v : ℕ → ℕ) :
    (Fml.and p q).Sat v ↔ p.Sat v ∧ q.Sat v := Iff.rfl

@[simp] theorem Fml.Sat_all (i : ℕ) (p : Fml) (v : ℕ → ℕ) :
    (Fml.all i p).Sat v ↔ ∀ m : ℕ, p.Sat (Function.update v i m) := Iff.rfl

@[simp] theorem Fml.Sat_imp (p q : Fml) (v : ℕ → ℕ) :
    (p.imp q).Sat v ↔ (p.Sat v → q.Sat v) := by
  simp only [Fml.imp, Fml.Sat_not, Fml.Sat_and, not_and, Classical.not_not]

@[simp] theorem Fml.Sat_ex (i : ℕ) (p : Fml) (v : ℕ → ℕ) :
    (Fml.ex i p).Sat v ↔ ∃ m : ℕ, p.Sat (Function.update v i m) := by
  simp only [Fml.ex, Fml.Sat_not, Fml.Sat_all, not_forall, Classical.not_not]

/-! ## Definability -/

/-- The assignment sending the variable `x₀` to `a` and all other variables to `0`. -/
def asg₁ (a : ℕ) : ℕ → ℕ := fun i => if i = 0 then a else 0

/-- The assignment sending `x₀` to `a`, `x₁` to `b` and all other variables to `0`. -/
def asg₂ (a b : ℕ) : ℕ → ℕ := fun i => if i = 0 then a else if i = 1 then b else 0

/-- `Sat₁ F a` says that `F` is true in `ℕ` when its variable `x₀` is given the
value `a` (and all other variables the value `0`). -/
def Sat₁ (F : Fml) (a : ℕ) : Prop := F.Sat (asg₁ a)

/-- `Sat₂ F a b` says that `F` is true in `ℕ` when `x₀ ↦ a` and `x₁ ↦ b`
(and all other variables get the value `0`). -/
def Sat₂ (F : Fml) (a b : ℕ) : Prop := F.Sat (asg₂ a b)

/-- A set of natural numbers is *arithmetical* if it is definable in the standard
model `ℕ` by a formula of the language of arithmetic in the free variable `x₀`. -/
def Arithmetical (S : Set ℕ) : Prop := ∃ F : Fml, ∀ a : ℕ, a ∈ S ↔ Sat₁ F a

/-- A binary relation on `ℕ` is *arithmetical* if it is definable in the standard
model `ℕ` by a formula in the free variables `x₀, x₁`. -/
def Arithmetical₂ (R : ℕ → ℕ → Prop) : Prop := ∃ F : Fml, ∀ a b : ℕ, R a b ↔ Sat₂ F a b

/-- `DefinesTruth T code` says that the formula `T`, in the two free variables
`x₀` (the code of a formula) and `x₁` (a value for the variable `x₀` of that
formula), defines arithmetical truth with respect to the Gödel numbering `code`:
for every formula `F` and every `a`, the formula `T` is true at `(⌜F⌝, a)` exactly
when `F` is true at `a` in the standard model. -/
def DefinesTruth (T : Fml) (code : Fml → ℕ) : Prop :=
  ∀ (F : Fml) (a : ℕ), Sat₂ T (code F) a ↔ Sat₁ F a

/-! ## The diagonal formula -/

/-- The diagonalisation of a two-variable formula `T`: the formula
`¬ ∀ x₁ (x₁ = x₀ → T)`, which is true at `a` exactly when `T` is false at `(a, a)`. -/
def diagFml (T : Fml) : Fml :=
  Fml.not (Fml.all 1 (Fml.imp (Fml.eq (Trm.var 1) (Trm.var 0)) T))

theorem update_asg₁_eq_asg₂ (a : ℕ) : Function.update (asg₁ a) 1 a = asg₂ a a := by
  funext i
  by_cases h : i = 1
  · subst h; simp [asg₂]
  · rw [Function.update_of_ne h]
    have h0 : ¬ (i = 1) := h
    simp only [asg₁, asg₂]
    by_cases h1 : i = 0 <;> simp [h1, h0]

theorem update_asg₁_apply_zero (a m : ℕ) : Function.update (asg₁ a) 1 m 0 = a := by
  rw [Function.update_of_ne (by norm_num)]
  simp [asg₁]

theorem update_asg₁_apply_one (a m : ℕ) : Function.update (asg₁ a) 1 m 1 = m := by
  simp

theorem Sat₁_diagFml (T : Fml) (a : ℕ) : Sat₁ (diagFml T) a ↔ ¬ Sat₂ T a a := by
  have key : (∀ m : ℕ, (Fml.imp (Fml.eq (Trm.var 1) (Trm.var 0)) T).Sat
      (Function.update (asg₁ a) 1 m)) ↔ Sat₂ T a a := by
    constructor
    · intro h
      have h' := h a
      simp only [Fml.Sat_imp, Fml.Sat_eq, Trm.eval, update_asg₁_apply_zero,
        update_asg₁_apply_one] at h'
      have h'' := h' rfl
      rwa [update_asg₁_eq_asg₂] at h''
    · intro h m
      simp only [Fml.Sat_imp, Fml.Sat_eq, Trm.eval, update_asg₁_apply_zero,
        update_asg₁_apply_one]
      rintro rfl
      rwa [update_asg₁_eq_asg₂]
  simp only [Sat₁, diagFml, Fml.Sat_not, Fml.Sat_all]
  rw [key]

/-! ## Tarski's undefinability theorem -/

/-- **Tarski's undefinability of truth.**  Arithmetical truth is not arithmetically
definable: there is no formula `T` of the language of arithmetic and no Gödel
numbering `code : Fml → ℕ` such that, for every formula `F` and every natural
number `a`, the formula `T` is true in `ℕ` at `(⌜F⌝, a)` if and only if `F` is
true in `ℕ` at `a`.

No effectiveness (not even injectivity) is assumed of the numbering `code`, so
the statement is stronger than the usual formulation for an effective Gödel
numbering. -/
theorem Tarski_undefinability :
    ¬ ∃ (T : Fml) (code : Fml → ℕ), DefinesTruth T code := by
  rintro ⟨T, code, hT⟩
  have h1 : Sat₁ (diagFml T) (code (diagFml T)) ↔ ¬ Sat₂ T (code (diagFml T)) (code (diagFml T)) :=
    Sat₁_diagFml T (code (diagFml T))
  have h2 : Sat₂ T (code (diagFml T)) (code (diagFml T)) ↔ Sat₁ (diagFml T) (code (diagFml T)) :=
    hT (diagFml T) (code (diagFml T))
  tauto

/-- Equivalent phrasing: no arithmetical binary relation is a truth (satisfaction)
predicate for the one-variable arithmetical formulas, under any numbering of
formulas. -/
theorem no_arithmetical_truth_relation :
    ¬ ∃ (R : ℕ → ℕ → Prop) (code : Fml → ℕ),
      Arithmetical₂ R ∧ ∀ (F : Fml) (a : ℕ), R (code F) a ↔ Sat₁ F a := by
  rintro ⟨R, code, ⟨T, hT⟩, hR⟩
  exact Tarski_undefinability ⟨T, code, fun F a => (hT (code F) a).symm.trans (hR F a)⟩

/-- Consequence: no arithmetical relation is universal for the arithmetical sets. -/
theorem no_universal_arithmetical_relation :
    ¬ ∃ R : ℕ → ℕ → Prop, Arithmetical₂ R ∧
      ∀ S : Set ℕ, Arithmetical S → ∃ e : ℕ, ∀ a : ℕ, a ∈ S ↔ R e a := by
  rintro ⟨R, ⟨T, hT⟩, huniv⟩
  have hdiag : Arithmetical {a : ℕ | ¬ R a a} := by
    refine ⟨diagFml T, fun a => ?_⟩
    rw [Sat₁_diagFml]
    exact not_congr (hT a a)
  obtain ⟨e, he⟩ := huniv _ hdiag
  have h := he e
  simp only [Set.mem_setOf_eq] at h
  tauto

/-- Consequence: the *diagonal truth set*, consisting of those numbers `n` such
that every formula with Gödel number `n` is true at `n`, is not arithmetical,
for any injective Gödel numbering. -/
theorem diagonal_truth_set_not_arithmetical (code : Fml → ℕ)
    (hcode : Function.Injective code) :
    ¬ Arithmetical {n : ℕ | ∀ F : Fml, code F = n → Sat₁ F n} := by
  rintro ⟨D, hD⟩
  have key : Sat₁ (Fml.not D) (code (Fml.not D)) ↔ ¬ Sat₁ D (code (Fml.not D)) := Iff.rfl
  have hmem : (code (Fml.not D)) ∈ {n : ℕ | ∀ F : Fml, code F = n → Sat₁ F n}
      ↔ Sat₁ (Fml.not D) (code (Fml.not D)) := by
    constructor
    · intro h; exact h (Fml.not D) rfl
    · intro h F hF
      have hFD : F = Fml.not D := hcode hF
      subst hFD
      simpa [hF] using h
  have h2 := hD (code (Fml.not D))
  rw [hmem, key] at h2
  tauto

/-! ## Non-triviality: the framework really does define sets -/

/-- The set of even numbers is arithmetical, witnessing that the notion
`Arithmetical` is not vacuous. -/
theorem arithmetical_even : Arithmetical {n : ℕ | Even n} := by
  refine ⟨Fml.ex 1 (Fml.eq (Trm.var 0) (Trm.add (Trm.var 1) (Trm.var 1))), fun a => ?_⟩
  simp only [Set.mem_setOf_eq, Sat₁, Fml.Sat_ex, Fml.Sat_eq, Trm.eval,
    update_asg₁_apply_zero, update_asg₁_apply_one]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩

/-! ## An injective Gödel numbering exists -/

/-- A Gödel numbering of terms. -/
def Trm.code : Trm → ℕ
  | Trm.var i => Nat.pair 0 i
  | Trm.zero => Nat.pair 1 0
  | Trm.succ t => Nat.pair 2 t.code
  | Trm.add t u => Nat.pair 3 (Nat.pair t.code u.code)
  | Trm.mul t u => Nat.pair 4 (Nat.pair t.code u.code)

theorem Trm.code_injective : Function.Injective Trm.code := by
  intro t u h
  induction t generalizing u with
  | var i => cases u <;> simp_all [Trm.code, Nat.pair_eq_pair]
  | zero => cases u <;> simp_all [Trm.code, Nat.pair_eq_pair]
  | succ t ih => cases u <;> simp_all [Trm.code, Nat.pair_eq_pair]; exact ih h
  | add t u iht ihu =>
      cases u <;> simp_all [Trm.code, Nat.pair_eq_pair]; exact ⟨iht h.1, ihu h.2⟩
  | mul t u iht ihu =>
      cases u <;> simp_all [Trm.code, Nat.pair_eq_pair]; exact ⟨iht h.1, ihu h.2⟩

/-- A Gödel numbering of formulas. -/
def Fml.code : Fml → ℕ
  | Fml.eq t u => Nat.pair 0 (Nat.pair t.code u.code)
  | Fml.not p => Nat.pair 1 p.code
  | Fml.and p q => Nat.pair 2 (Nat.pair p.code q.code)
  | Fml.all i p => Nat.pair 3 (Nat.pair i p.code)

theorem Fml.code_injective : Function.Injective Fml.code := by
  intro p q h
  induction p generalizing q with
  | eq t u => cases q <;> simp_all [Fml.code, Nat.pair_eq_pair, Trm.code_injective.eq_iff]
  | not p ih => cases q <;> simp_all [Fml.code, Nat.pair_eq_pair]; exact ih h
  | and p q ihp ihq =>
      cases q <;> simp_all [Fml.code, Nat.pair_eq_pair]; exact ⟨ihp h.1, ihq h.2⟩
  | all i p ih => cases q <;> simp_all [Fml.code, Nat.pair_eq_pair]; exact ih h.2

/-- With the concrete (injective) Gödel numbering `Fml.code`, the diagonal truth
set is not arithmetical. -/
theorem diagonal_truth_set_not_arithmetical' :
    ¬ Arithmetical {n : ℕ | ∀ F : Fml, Fml.code F = n → Sat₁ F n} :=
  diagonal_truth_set_not_arithmetical Fml.code Fml.code_injective

end Frontier

