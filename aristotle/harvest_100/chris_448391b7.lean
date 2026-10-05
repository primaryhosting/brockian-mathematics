/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires
-- module doc comments to appear *after* the `import` lines.)

import Mathlib

/-!
## Overview

We formalize Tarski's undefinability theorem: the set of (Gödel numbers of) true
arithmetical sentences is not definable by any arithmetical formula.

Everything is built from scratch:

* `Frontier.Tarski.Trm` : terms of the language of arithmetic `(0, S, +, ·)`,
  with variables indexed by `ℕ`;
* `Frontier.Tarski.Fml` : formulas, built from equations by negation,
  conjunction, universal quantification, and a *parameter* constructor
  `Fml.subst n φ`, which denotes `φ` with the numeral `n` substituted for the
  variable `v₀` (this constructor is eliminable, see `Fml.purify`);
* `Frontier.Tarski.Fml.Sat` : the standard satisfaction relation in the
  structure `ℕ`;
* `Frontier.Tarski.Fml.code` : an injective Gödel numbering
  (`Frontier.Tarski.Fml.code_injective`);
* `Frontier.Tarski.TruthSet` : the set of codes of true sentences;
* `Frontier.Tarski.Definable` : the sets of naturals definable by a formula.

The main theorem is `Frontier.Tarski_undefinability : ¬ Definable TruthSet`.
-/

namespace Frontier
namespace Tarski

/-! ## Syntax -/

/-- Terms of the language of arithmetic, with variables indexed by `ℕ`. -/
inductive Trm : Type
  | var : ℕ → Trm
  | zero : Trm
  | succ : Trm → Trm
  | add : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Value of a term under an assignment `ρ` of naturals to the variables. -/
def eval (ρ : ℕ → ℕ) : Trm → ℕ
  | var i => ρ i
  | zero => 0
  | succ t => eval ρ t + 1
  | add t u => eval ρ t + eval ρ u
  | mul t u => eval ρ t * eval ρ u

/-- The set of variables occurring in a term. -/
def fv : Trm → Finset ℕ
  | var i => {i}
  | zero => ∅
  | succ t => fv t
  | add t u => fv t ∪ fv u
  | mul t u => fv t ∪ fv u

/-- The `n`-th numeral `S (S (… (S 0)))`. -/
def numeral : ℕ → Trm
  | 0 => zero
  | (n + 1) => succ (numeral n)

@[simp] lemma eval_numeral (ρ : ℕ → ℕ) (n : ℕ) : (numeral n).eval ρ = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, eval, ih]

@[simp] lemma fv_numeral (n : ℕ) : (numeral n).fv = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [numeral, fv] using ih

/-- The value of a term only depends on the assignment at its variables. -/
lemma eval_congr {ρ ρ' : ℕ → ℕ} : ∀ (t : Trm), (∀ i ∈ t.fv, ρ i = ρ' i) →
    t.eval ρ = t.eval ρ'
  | var i, h => h i (by simp [fv])
  | zero, _ => rfl
  | succ t, h => by simp [eval, eval_congr t h]
  | add t u, h => by
      simp only [eval]
      rw [eval_congr t (fun i hi => h i (by simp [fv, hi])),
        eval_congr u (fun i hi => h i (by simp [fv, hi]))]
  | mul t u, h => by
      simp only [eval]
      rw [eval_congr t (fun i hi => h i (by simp [fv, hi])),
        eval_congr u (fun i hi => h i (by simp [fv, hi]))]

/-- Substitution of the term `s` for the variable `v₀`. -/
def subst0 (s : Trm) : Trm → Trm
  | var i => if i = 0 then s else var i
  | zero => zero
  | succ t => succ (subst0 s t)
  | add t u => add (subst0 s t) (subst0 s u)
  | mul t u => mul (subst0 s t) (subst0 s u)

lemma eval_subst0 (s : Trm) (ρ : ℕ → ℕ) : ∀ t : Trm,
    (subst0 s t).eval ρ = t.eval (Function.update ρ 0 (s.eval ρ))
  | var i => by
      by_cases h : i = 0 <;> simp [subst0, eval, h, Function.update]
  | zero => rfl
  | succ t => by simp [subst0, eval, eval_subst0 s ρ t]
  | add t u => by simp [subst0, eval, eval_subst0 s ρ t, eval_subst0 s ρ u]
  | mul t u => by simp [subst0, eval, eval_subst0 s ρ t, eval_subst0 s ρ u]

lemma fv_subst0 (s : Trm) : ∀ t : Trm, (subst0 s t).fv ⊆ t.fv.erase 0 ∪ s.fv
  | var i => by
      by_cases h : i = 0
      · subst h
        intro x hx
        simp only [subst0, if_pos rfl] at hx
        simp [hx]
      · intro x hx
        simp only [subst0, if_neg h, fv, Finset.mem_singleton] at hx
        subst hx
        simp [fv, h]
  | zero => by simp [subst0, fv]
  | succ t => fv_subst0 s t
  | add t u => by
      intro x hx
      simp only [subst0, fv, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have h1 := fv_subst0 s t hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
      · have h1 := fv_subst0 s u hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | mul t u => by
      intro x hx
      simp only [subst0, fv, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have h1 := fv_subst0 s t hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
      · have h1 := fv_subst0 s u hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto

/-- Gödel numbering of terms. -/
def code : Trm → ℕ
  | var i => 5 * i
  | zero => 1
  | succ t => 5 * code t + 2
  | add t u => 5 * Nat.pair (code t) (code u) + 3
  | mul t u => 5 * Nat.pair (code t) (code u) + 4

lemma code_injective : Function.Injective code := by
  intro t
  induction t with
  | var i => intro u h; cases u <;> simp [code] at h ⊢ <;> omega
  | zero => intro u h; cases u <;> simp [code] at h ⊢ <;> omega
  | succ t ih =>
      intro u h; cases u <;> simp only [code] at h
      · omega
      · omega
      · exact congrArg succ (ih (by omega))
      · omega
      · omega
  | add t u iht ihu =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · omega
      · case add a b =>
          have hp : Nat.pair (code t) (code u) = Nat.pair (code a) (code b) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          exact congrArg₂ add (iht this.1) (ihu this.2)
      · omega
  | mul t u iht ihu =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · omega
      · omega
      · case mul a b =>
          have hp : Nat.pair (code t) (code u) = Nat.pair (code a) (code b) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          exact congrArg₂ mul (iht this.1) (ihu this.2)

end Trm

/-- Formulas of the language of arithmetic.  Besides equations, negation,
conjunction and universal quantification, there is a constructor `subst n φ`
denoting the result of substituting the numeral `n` for the variable `v₀` in
`φ`.  This constructor is eliminable: see `Fml.purify` and `Fml.sat_purify`. -/
inductive Fml : Type
  | eq : Trm → Trm → Fml
  | not : Fml → Fml
  | and : Fml → Fml → Fml
  | all : ℕ → Fml → Fml
  | subst : ℕ → Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Satisfaction in the standard model `ℕ`, relative to an assignment `ρ`. -/
def Sat : Fml → (ℕ → ℕ) → Prop
  | eq t u, ρ => t.eval ρ = u.eval ρ
  | not φ, ρ => ¬ Sat φ ρ
  | and φ ψ, ρ => Sat φ ρ ∧ Sat ψ ρ
  | all i φ, ρ => ∀ n : ℕ, Sat φ (Function.update ρ i n)
  | subst n φ, ρ => Sat φ (Function.update ρ 0 n)

/-- The set of free variables of a formula. -/
def fv : Fml → Finset ℕ
  | eq t u => t.fv ∪ u.fv
  | not φ => fv φ
  | and φ ψ => fv φ ∪ fv ψ
  | all i φ => (fv φ).erase i
  | subst _ φ => (fv φ).erase 0

/-- A sentence is a formula without free variables. -/
def IsSentence (φ : Fml) : Prop := φ.fv = ∅

/-- Truth in the standard model: satisfaction under the everywhere-zero
assignment.  For sentences this does not depend on the assignment, see
`Fml.trueIn_iff_forall`. -/
def TrueIn (φ : Fml) : Prop := φ.Sat (fun _ => 0)

/-- Satisfaction only depends on the assignment at the free variables. -/
lemma sat_congr : ∀ (φ : Fml) {ρ ρ' : ℕ → ℕ}, (∀ i ∈ φ.fv, ρ i = ρ' i) →
    (φ.Sat ρ ↔ φ.Sat ρ')
  | eq t u, ρ, ρ', h => by
      simp only [Sat]
      rw [Trm.eval_congr t (fun i hi => h i (by simp [fv, hi])),
        Trm.eval_congr u (fun i hi => h i (by simp [fv, hi]))]
  | not φ, ρ, ρ', h => by
      simp only [Sat]
      exact not_congr (sat_congr φ h)
  | and φ ψ, ρ, ρ', h => by
      simp only [Sat]
      exact and_congr (sat_congr φ (fun i hi => h i (by simp [fv, hi])))
        (sat_congr ψ (fun i hi => h i (by simp [fv, hi])))
  | all i φ, ρ, ρ', h => by
      simp only [Sat]
      refine forall_congr' (fun n => sat_congr φ ?_)
      intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact h j (by simp [fv, Finset.mem_erase, hji, hj])
  | subst n φ, ρ, ρ', h => by
      simp only [Sat]
      refine sat_congr φ ?_
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp
      · rw [Function.update_of_ne hj0, Function.update_of_ne hj0]
        exact h j (by simp [fv, Finset.mem_erase, hj0, hj])

/-- For a sentence, truth in `ℕ` does not depend on the assignment. -/
lemma trueIn_iff_forall {φ : Fml} (hφ : φ.IsSentence) :
    φ.TrueIn ↔ ∀ ρ : ℕ → ℕ, φ.Sat ρ := by
  constructor
  · intro h ρ
    exact (sat_congr φ (fun i hi => by rw [hφ] at hi; exact absurd hi (by simp))).1 h
  · intro h; exact h _

/-- Substitution of the term `s` for the variable `v₀` in a formula. -/
def subst0 (s : Trm) : Fml → Fml
  | eq t u => eq (Trm.subst0 s t) (Trm.subst0 s u)
  | not φ => not (subst0 s φ)
  | and φ ψ => and (subst0 s φ) (subst0 s ψ)
  | all i φ => if i = 0 then all i φ else all i (subst0 s φ)
  | subst n φ => subst n φ

/-- Substituting a term `s` whose only variable is `v₀` behaves semantically as
expected. -/
lemma sat_subst0 {s : Trm} (hs : s.fv ⊆ {0}) : ∀ (φ : Fml) (ρ : ℕ → ℕ),
    (subst0 s φ).Sat ρ ↔ φ.Sat (Function.update ρ 0 (s.eval ρ))
  | eq t u, ρ => by
      simp only [subst0, Sat, Trm.eval_subst0 s ρ t, Trm.eval_subst0 s ρ u]
  | not φ, ρ => by simp [subst0, Sat, sat_subst0 hs φ ρ]
  | and φ ψ, ρ => by simp [subst0, Sat, sat_subst0 hs φ ρ, sat_subst0 hs ψ ρ]
  | all i φ, ρ => by
      by_cases hi : i = 0
      · subst hi
        simp only [subst0, if_pos rfl, Sat]
        refine forall_congr' (fun n => ?_)
        rw [Function.update_idem]
      · simp only [subst0, if_neg hi, Sat]
        refine forall_congr' (fun n => ?_)
        rw [sat_subst0 hs φ]
        have hev : s.eval (Function.update ρ i n) = s.eval ρ := by
          refine Trm.eval_congr s (fun j hj => ?_)
          have hj0 : j = 0 := by simpa using hs hj
          simp [hj0, Ne.symm hi]
        rw [hev, Function.update_comm (Ne.symm hi)]
  | subst n φ, ρ => by
      simp only [subst0, Sat]
      rw [Function.update_idem]

lemma fv_subst0 {s : Trm} : ∀ (φ : Fml), (subst0 s φ).fv ⊆ φ.fv.erase 0 ∪ s.fv
  | eq t u => by
      intro x hx
      simp only [subst0, fv, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have h1 := Trm.fv_subst0 s t hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
      · have h1 := Trm.fv_subst0 s u hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | not φ => fv_subst0 φ
  | and φ ψ => by
      intro x hx
      simp only [subst0, fv, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have h1 := fv_subst0 (s := s) φ hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
      · have h1 := fv_subst0 (s := s) ψ hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | all i φ => by
      intro x hx
      by_cases hi : i = 0
      · subst hi
        simp only [subst0, if_pos rfl, fv, Finset.mem_erase] at hx
        simp only [Finset.mem_union, Finset.mem_erase, fv]
        tauto
      · simp only [subst0, if_neg hi, fv, Finset.mem_erase] at hx
        have h1 := fv_subst0 (s := s) φ hx.2
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | subst n φ => by
      intro x hx
      simp only [subst0, fv, Finset.mem_erase] at hx
      simp only [Finset.mem_union, Finset.mem_erase, fv]
      tauto

/-- Gödel numbering of formulas. -/
def code : Fml → ℕ
  | eq t u => 5 * Nat.pair t.code u.code
  | not φ => 5 * code φ + 1
  | and φ ψ => 5 * Nat.pair (code φ) (code ψ) + 2
  | all i φ => 5 * Nat.pair i (code φ) + 3
  | subst n φ => 5 * Nat.pair n (code φ) + 4

lemma code_injective : Function.Injective code := by
  intro φ
  induction φ with
  | eq t u =>
      intro w h; cases w <;> simp only [code] at h
      · case eq a b =>
          have hp : Nat.pair t.code u.code = Nat.pair a.code b.code := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          exact congrArg₂ eq (Trm.code_injective this.1) (Trm.code_injective this.2)
      · omega
      · omega
      · omega
      · omega
  | not φ ih =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · exact congrArg not (ih (by omega))
      · omega
      · omega
      · omega
  | and φ ψ ihφ ihψ =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · case and a b =>
          have hp : Nat.pair (code φ) (code ψ) = Nat.pair (code a) (code b) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          exact congrArg₂ and (ihφ this.1) (ihψ this.2)
      · omega
      · omega
  | all i φ ih =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · omega
      · case all j a =>
          have hp : Nat.pair i (code φ) = Nat.pair j (code a) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          rw [this.1, ih this.2]
      · omega
  | subst n φ ih =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · omega
      · omega
      · case subst m a =>
          have hp : Nat.pair n (code φ) = Nat.pair m (code a) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          rw [this.1, ih this.2]

/-! ### Eliminability of the parameter constructor -/

/-- A formula is *pure* if it does not use the parameter constructor `subst`,
i.e. it is a formula of the plain language of arithmetic. -/
def IsPure : Fml → Prop
  | eq _ _ => True
  | not φ => IsPure φ
  | and φ ψ => IsPure φ ∧ IsPure ψ
  | all _ φ => IsPure φ
  | subst _ _ => False

lemma isPure_subst0 {s : Trm} : ∀ {φ : Fml}, IsPure φ → IsPure (subst0 s φ)
  | eq _ _, _ => trivial
  | not φ, h => isPure_subst0 (φ := φ) h
  | and φ ψ, h => ⟨isPure_subst0 (φ := φ) h.1, isPure_subst0 (φ := ψ) h.2⟩
  | all i φ, h => by
      by_cases hi : i = 0
      · simpa [subst0, hi, IsPure] using h
      · simpa [subst0, hi, IsPure] using isPure_subst0 (φ := φ) h

/-- Turning a formula into an equivalent pure formula, by replacing the
parameters with the corresponding numerals. -/
def purify : Fml → Fml
  | eq t u => eq t u
  | not φ => not (purify φ)
  | and φ ψ => and (purify φ) (purify ψ)
  | all i φ => all i (purify φ)
  | subst n φ => subst0 (Trm.numeral n) (purify φ)

lemma isPure_purify : ∀ φ : Fml, IsPure (purify φ)
  | eq _ _ => trivial
  | not φ => isPure_purify φ
  | and φ ψ => ⟨isPure_purify φ, isPure_purify ψ⟩
  | all _ φ => isPure_purify φ
  | subst _ φ => isPure_subst0 (isPure_purify φ)

lemma sat_purify : ∀ (φ : Fml) (ρ : ℕ → ℕ), (purify φ).Sat ρ ↔ φ.Sat ρ
  | eq _ _, _ => Iff.rfl
  | not φ, ρ => by simp [purify, Sat, sat_purify φ ρ]
  | and φ ψ, ρ => by simp [purify, Sat, sat_purify φ ρ, sat_purify ψ ρ]
  | all i φ, ρ => by
      simp only [purify, Sat]
      exact forall_congr' fun n => sat_purify φ _
  | subst n φ, ρ => by
      simp only [purify, Sat]
      rw [sat_subst0 (by simp) (purify φ) ρ, sat_purify φ]
      simp

end Fml

/-! ## Arithmetical truth and definability -/

/-- The set of Gödel numbers of true arithmetical sentences. -/
def TruthSet : Set ℕ := {n | ∃ φ : Fml, φ.IsSentence ∧ φ.code = n ∧ φ.TrueIn}

/-- A set of naturals is *arithmetically definable* if there is a formula `T`
whose only possible free variable is `v₀` such that, for every `n`, the sentence
`T(n)` is true in `ℕ` exactly when `n` belongs to the set. -/
def Definable (S : Set ℕ) : Prop :=
  ∃ T : Fml, T.fv ⊆ {0} ∧ ∀ n : ℕ, ((Fml.subst n T).TrueIn ↔ n ∈ S)

/-- The term `5 * (x₀ * x₀ + x₀ + x₀) + 4`, which computes the Gödel number of
the diagonal sentence `subst e ψ` from the Gödel number `e` of `ψ`. -/
def diagTrm : Trm :=
  Trm.add
    (Trm.mul (Trm.numeral 5)
      (Trm.add (Trm.add (Trm.mul (Trm.var 0) (Trm.var 0)) (Trm.var 0)) (Trm.var 0)))
    (Trm.numeral 4)

@[simp] lemma diagTrm_fv : diagTrm.fv = {0} := by
  simp [diagTrm, Trm.fv]

lemma diagTrm_eval (ρ : ℕ → ℕ) :
    diagTrm.eval ρ = 5 * Nat.pair (ρ 0) (ρ 0) + 4 := by
  have : Nat.pair (ρ 0) (ρ 0) = ρ 0 * ρ 0 + ρ 0 + ρ 0 := by
    simp [Nat.pair]
  simp [diagTrm, Trm.eval, this]

end Tarski

open Tarski in
/-- **Tarski's undefinability theorem.**  The set of Gödel numbers of true
arithmetical sentences is not definable by any arithmetical formula. -/
theorem Tarski_undefinability : ¬ Definable TruthSet := by
  rintro ⟨T, hTfv, hT⟩
  -- the diagonal formula `ψ(x) := ¬ T(5 * pair(x, x) + 4)`
  set ψ : Fml := Fml.not (Fml.subst0 diagTrm T) with hψ
  have hψfv : ψ.fv ⊆ {0} := by
    intro x hx
    have hx' : x ∈ (Fml.subst0 diagTrm T).fv := hx
    have := Fml.fv_subst0 (s := diagTrm) T hx'
    simp only [Finset.mem_union, Finset.mem_erase, diagTrm_fv, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hTfv h.2
    · simpa using h
  set e : ℕ := ψ.code with he
  set σ : Fml := Fml.subst e ψ with hσ
  have hσsent : σ.IsSentence := by
    have hfv : σ.fv = ψ.fv.erase 0 := rfl
    show σ.fv = ∅
    rw [hfv]
    refine Finset.eq_empty_of_forall_notMem ?_
    intro x hx
    rcases Finset.mem_erase.1 hx with ⟨hx0, hxψ⟩
    exact hx0 (by simpa using hψfv hxψ)
  have hcode : σ.code = 5 * Nat.pair e e + 4 := rfl
  -- the key equivalence
  have key : σ.TrueIn ↔ ¬ (Fml.subst σ.code T).TrueIn := by
    have h1 : σ.TrueIn ↔ ¬ (Fml.subst0 diagTrm T).Sat (Function.update (fun _ => 0) 0 e) :=
      Iff.rfl
    rw [h1, Fml.sat_subst0 (by simp) T]
    have h2 : diagTrm.eval (Function.update (fun _ : ℕ => 0) 0 e) = σ.code := by
      rw [diagTrm_eval, hcode]
      simp
    rw [h2, Function.update_idem]
    rfl
  have hmem : σ.code ∈ TruthSet ↔ σ.TrueIn := by
    constructor
    · rintro ⟨φ, _, hcodeφ, hφ⟩
      have : φ = σ := Fml.code_injective hcodeφ
      exact this ▸ hφ
    · intro h; exact ⟨σ, hσsent, rfl, h⟩
  rw [hT σ.code, hmem] at key
  tauto

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

