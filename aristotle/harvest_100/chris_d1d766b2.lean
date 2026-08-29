/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file is deliberately self-contained (it needs no imports): it develops the
syntax and the standard-model semantics of first-order arithmetic from scratch and
proves Tarski's undefinability theorem for it.
-/

namespace Frontier

/-! ## Syntax of first-order arithmetic

Variables are indexed by natural numbers.  Terms are built from `0`, the successor
function, addition and multiplication; formulas are built from equations between
terms using negation, conjunction and universal quantification (the remaining
connectives and the existential quantifier are definable from these). -/

/-- Terms of the language of arithmetic. -/
inductive ATerm where
  | var : Nat → ATerm
  | zero : ATerm
  | succ : ATerm → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq

/-- Formulas of the language of arithmetic. -/
inductive AFormula where
  | eq : ATerm → ATerm → AFormula
  | not : AFormula → AFormula
  | and : AFormula → AFormula → AFormula
  | all : Nat → AFormula → AFormula
  deriving DecidableEq

/-! ## Semantics: the standard model `Nat` -/

/-- Value of a term in the standard model `Nat` under an assignment of the variables. -/
def ATerm.eval : ATerm → (Nat → Nat) → Nat
  | .var i, e => e i
  | .zero, _ => 0
  | .succ t, e => t.eval e + 1
  | .add a b, e => a.eval e + b.eval e
  | .mul a b, e => a.eval e * b.eval e

/-- Satisfaction of a formula in the standard model `Nat` under an assignment of the
variables: this is *arithmetical truth*. -/
def Sat : AFormula → (Nat → Nat) → Prop
  | .eq a b, e => a.eval e = b.eval e
  | .not p, e => ¬ Sat p e
  | .and p q, e => Sat p e ∧ Sat q e
  | .all i p, e => ∀ m : Nat, Sat p (fun j => if j = i then m else e j)

@[simp] theorem Sat_not (p : AFormula) (e : Nat → Nat) : Sat (.not p) e ↔ ¬ Sat p e := Iff.rfl

/-- A binary relation on `Nat` is *arithmetical* (arithmetically definable) if it is
defined in the standard model by a formula of arithmetic, with the variables `x₀`
and `x₁` as its two argument places. -/
def Definable₂ (R : Nat → Nat → Prop) : Prop :=
  ∃ φ : AFormula, ∀ a b : Nat, R a b ↔ Sat φ (fun i => if i = 0 then a else b)

/-! ### Sanity checks: some arithmetical relations -/

/-- Equality is arithmetical. -/
theorem definable_eq : Definable₂ (fun a b => a = b) :=
  ⟨.eq (.var 0) (.var 1), by intro a b; simp [Sat, ATerm.eval]⟩

/-- Doubling is arithmetical. -/
theorem definable_double : Definable₂ (fun a b => a + a = b) :=
  ⟨.eq (.add (.var 0) (.var 0)) (.var 1), by intro a b; simp [Sat, ATerm.eval]⟩

/-- A relation defined with a universal quantifier is arithmetical. -/
theorem definable_forall : Definable₂ (fun a b => ∀ c : Nat, a * c = b * c) :=
  ⟨.all 2 (.eq (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))), by
    intro a b; simp [Sat, ATerm.eval]⟩

/-! ## Tarski's undefinability theorem

`Frontier.Tarski_undefinability` says: for no Gödel numbering `code` of formulas is
there a formula `tr` of arithmetic defining arithmetical truth, i.e. such that
`tr(⌜φ⌝, n)` holds in the standard model exactly when `φ` holds in the standard model
under the assignment sending every variable to `n`.  In other words, the satisfaction
relation of arithmetic is not itself arithmetically definable.

No assumption whatsoever is made on the coding function `code` (it need not even be
injective or computable), which makes the statement as strong as possible. -/
theorem Tarski_undefinability :
    ¬ ∃ (tr : AFormula) (code : AFormula → Nat),
        ∀ (φ : AFormula) (n : Nat),
          Sat tr (fun i => if i = 0 then code φ else n) ↔ Sat φ (fun _ => n) := by
  rintro ⟨tr, code, h⟩
  -- The diagonal formula: the negation of the alleged truth predicate.
  have key := h (.not tr) (code (.not tr))
  have henv :
      (fun i : Nat => if i = 0 then code (.not tr) else code (.not tr))
        = (fun _ : Nat => code (.not tr)) := by
    funext i; split <;> rfl
  rw [henv, Sat_not] at key
  have hn : ¬ Sat tr (fun _ : Nat => code (.not tr)) := fun hk => key.mp hk hk
  exact hn (key.mpr hn)

/-- **Tarski's undefinability theorem**, phrased in terms of definable relations:
for any injective Gödel numbering `code` of the formulas of arithmetic, the truth
relation `{(⌜φ⌝, n) : φ holds in the standard model under the assignment constantly
equal to n}` is not arithmetically definable. -/
theorem truth_not_definable (code : AFormula → Nat) (hcode : Function.Injective code) :
    ¬ Definable₂ (fun a b => ∃ φ : AFormula, code φ = a ∧ Sat φ (fun _ => b)) := by
  rintro ⟨tr, htr⟩
  refine Tarski_undefinability ⟨tr, code, fun φ n => ?_⟩
  rw [← htr (code φ) n]
  constructor
  · rintro ⟨ψ, hψ, hsat⟩
    rwa [hcode hψ] at hsat
  · exact fun hsat => ⟨φ, rfl, hsat⟩

/-! ## Existence of Gödel numberings

The syntax of arithmetic is countable, so injective codings as in
`Frontier.truth_not_definable` do exist; in particular that statement is not vacuous. -/

/-- An injective pairing function on `Nat`. -/
def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem pair_inj {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  induction a generalizing c with
  | zero =>
      cases c with
      | zero => simp [pair] at h; omega
      | succ c =>
          exfalso
          have : 2 * b + 1 = 2 * (2 ^ c * (2 * d + 1)) := by
            simpa [pair, Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h
          omega
  | succ a ih =>
      cases c with
      | zero =>
          exfalso
          have : 2 * (2 ^ a * (2 * b + 1)) = 2 * d + 1 := by
            simpa [pair, Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h
          omega
      | succ c =>
          have h2 : 2 * (2 ^ a * (2 * b + 1)) = 2 * (2 ^ c * (2 * d + 1)) := by
            simpa [pair, Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h
          have h3 : pair a b = pair c d := by
            simp only [pair]; omega
          have := ih h3
          exact ⟨by omega, this.2⟩

/-- An explicit Gödel numbering of terms. -/
def encodeTerm : ATerm → Nat
  | .var i => pair 0 i
  | .zero => pair 1 0
  | .succ t => pair 2 (encodeTerm t)
  | .add a b => pair 3 (pair (encodeTerm a) (encodeTerm b))
  | .mul a b => pair 4 (pair (encodeTerm a) (encodeTerm b))

theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro s
  induction s with
  | var i =>
      intro t hst
      cases t <;> simp only [encodeTerm] at hst <;>
        first
          | (have := pair_inj hst; simp_all)
          | (have := (pair_inj hst).1; omega)
  | zero =>
      intro t hst
      cases t <;> simp only [encodeTerm] at hst <;>
        first
          | rfl
          | (have := (pair_inj hst).1; omega)
  | succ s ih =>
      intro t hst
      cases t <;> simp only [encodeTerm] at hst <;>
        first
          | (have := (pair_inj hst).1; omega)
          | (rw [ih (pair_inj hst).2])
  | add s1 s2 ih1 ih2 =>
      intro t hst
      cases t <;> simp only [encodeTerm] at hst <;>
        first
          | (have := (pair_inj hst).1; omega)
          | (have h2 := pair_inj (pair_inj hst).2
             rw [ih1 h2.1, ih2 h2.2])
  | mul s1 s2 ih1 ih2 =>
      intro t hst
      cases t <;> simp only [encodeTerm] at hst <;>
        first
          | (have := (pair_inj hst).1; omega)
          | (have h2 := pair_inj (pair_inj hst).2
             rw [ih1 h2.1, ih2 h2.2])

/-- An explicit Gödel numbering of formulas. -/
def encodeFormula : AFormula → Nat
  | .eq a b => pair 0 (pair (encodeTerm a) (encodeTerm b))
  | .not p => pair 1 (encodeFormula p)
  | .and p q => pair 2 (pair (encodeFormula p) (encodeFormula q))
  | .all i p => pair 3 (pair i (encodeFormula p))

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro p
  induction p with
  | eq a b =>
      intro q hpq
      cases q <;> simp only [encodeFormula] at hpq <;>
        first
          | (have := (pair_inj hpq).1; omega)
          | (have h2 := pair_inj (pair_inj hpq).2
             rw [encodeTerm_injective h2.1, encodeTerm_injective h2.2])
  | not p ih =>
      intro q hpq
      cases q <;> simp only [encodeFormula] at hpq <;>
        first
          | (have := (pair_inj hpq).1; omega)
          | (rw [ih (pair_inj hpq).2])
  | and p1 p2 ih1 ih2 =>
      intro q hpq
      cases q <;> simp only [encodeFormula] at hpq <;>
        first
          | (have := (pair_inj hpq).1; omega)
          | (have h2 := pair_inj (pair_inj hpq).2
             rw [ih1 h2.1, ih2 h2.2])
  | all i p ih =>
      intro q hpq
      cases q <;> simp only [encodeFormula] at hpq <;>
        first
          | (have := (pair_inj hpq).1; omega)
          | (have h2 := pair_inj (pair_inj hpq).2
             rw [ih h2.2, h2.1])

/-- Tarski's theorem applied to the explicit Gödel numbering `encodeFormula`: the set
of (codes of) true formulas of arithmetic is not arithmetically definable. -/
theorem truth_not_definable_encodeFormula :
    ¬ Definable₂ (fun a b => ∃ φ : AFormula, encodeFormula φ = a ∧ Sat φ (fun _ => b)) :=
  truth_not_definable encodeFormula encodeFormula_injective

end Frontier

import Mathlib
import RequestProject.TarskiUndefinability

/-!
# Tarski Undefinability — Mathlib interface

Restatements of the results of `RequestProject.TarskiUndefinability` in Mathlib
vocabulary (`Set`, `Countable`), together with the fact that the syntax of arithmetic
is countable, so that injective Gödel numberings exist.
-/

namespace Frontier

/-- The formulas of arithmetic form a countable type. -/
instance : Countable AFormula := encodeFormula_injective.countable

/-- Injective Gödel numberings of the formulas of arithmetic exist. -/
theorem exists_injective_coding : ∃ code : AFormula → ℕ, Function.Injective code :=
  ⟨encodeFormula, encodeFormula_injective⟩

/-- The set of pairs `(⌜φ⌝, n)` such that `φ` holds in the standard model under the
assignment constantly equal to `n`: the arithmetical truth set relative to a Gödel
numbering `code`. -/
def truthSet (code : AFormula → ℕ) : Set (ℕ × ℕ) :=
  {p | ∃ φ : AFormula, code φ = p.1 ∧ Sat φ (fun _ => p.2)}

/-- The set of pairs defined in the standard model by a formula `φ` of arithmetic,
using `x₀` and `x₁` as its two argument places. -/
def definedSet (φ : AFormula) : Set (ℕ × ℕ) :=
  {p | Sat φ (fun i => if i = 0 then p.1 else p.2)}

/-- **Tarski's undefinability theorem**, in `Set` form: for every injective Gödel
numbering, the arithmetical truth set is not the set defined by any formula of
arithmetic. -/
theorem truthSet_ne_definedSet (code : AFormula → ℕ) (hcode : Function.Injective code)
    (φ : AFormula) : truthSet code ≠ definedSet φ := by
  intro h
  refine truth_not_definable code hcode ⟨φ, fun a b => ?_⟩
  have := Set.ext_iff.mp h (a, b)
  simpa [truthSet, definedSet] using this

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

