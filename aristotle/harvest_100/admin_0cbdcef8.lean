/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic and its standard model

We work with the usual first-order language of arithmetic, with constants `0` and `1`,
binary function symbols `+` and `*`, and the binary relation symbol `≤`, interpreted in
the standard model `ℕ`.
-/

/-- Function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- Relation symbols of the language of arithmetic: `≤`. -/
inductive arithRel : ℕ → Type
  | le : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic. -/
def arith : FirstOrder.Language := ⟨arithFunc, arithRel⟩

/-- The standard model: `ℕ` with its usual arithmetic. -/
instance arithStructureNat : arith.Structure ℕ where
  funMap {n} f ts := match n, f with
    | _, arithFunc.zero => 0
    | _, arithFunc.one => 1
    | _, arithFunc.add => ts 0 + ts 1
    | _, arithFunc.mul => ts 0 * ts 1
  RelMap {n} r ts := match n, r with
    | _, arithRel.le => ts 0 ≤ ts 1

/-- The closed term `0`. -/
def zeroTerm {α : Type} : arith.Term α :=
  Term.func (L := arith) arithFunc.zero (fun i => i.elim0)

/-- The closed term `1`. -/
def oneTerm {α : Type} : arith.Term α :=
  Term.func (L := arith) arithFunc.one (fun i => i.elim0)

/-- The sum of two terms. -/
def addTerm {α : Type} (s t : arith.Term α) : arith.Term α :=
  Term.func (L := arith) arithFunc.add ![s, t]

/-- The numeral denoting a natural number `n`: the closed term `0 + 1 + ⋯ + 1` (`n` summands). -/
def numeral {α : Type} : ℕ → arith.Term α
  | 0 => zeroTerm
  | (n + 1) => addTerm (numeral n) oneTerm

@[simp]
theorem realize_numeral {α : Type} (v : α → ℕ) (n : ℕ) :
    Term.realize v (numeral n : arith.Term α) = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show Term.realize v (numeral k) + Term.realize v (oneTerm : arith.Term α) = k + 1
      rw [ih]
      rfl

/-! ## Tarski's undefinability theorem

The key semantic content of Tarski's theorem is that no arithmetical formula can act as a
*universal* (satisfaction/truth) predicate for arithmetical formulas: whatever way one tries to
index the formulas by natural numbers, no single binary formula `θ(x, y)` can express
"the formula indexed by `x` is satisfied by `y`".

Note that the statement below quantifies existentially over the index `e`, so it rules out
truth definitions relative to *every* possible Gödel numbering at once.
-/

/-- **Tarski's undefinability of truth.**

There is no arithmetical formula `θ(x, y)` which is universal for the arithmetical formulas in
one free variable: i.e. such that every formula `p(y)` has some code `e` with
`ℕ ⊨ θ(e, n) ↔ ℕ ⊨ p(n)` for all `n`.

Equivalently: the satisfaction (truth) relation of the standard model of arithmetic is not
itself arithmetically definable. The proof is Tarski's diagonal argument: apply the assumed
universal formula to the diagonal formula `¬θ(y, y)`. -/
theorem Tarski_undefinability :
    ¬ ∃ θ : arith.Formula (Fin 2),
        ∀ p : arith.Formula (Fin 1), ∃ e : ℕ,
          ∀ n : ℕ, (θ.Realize (M := ℕ) ![e, n] ↔ p.Realize ![n]) := by
  rintro ⟨θ, hθ⟩
  -- The diagonal formula `p(y) := ¬ θ(y, y)`.
  obtain ⟨e, he⟩ := hθ (∼ (θ.relabel (fun _ => 0)))
  have h := he e
  rw [Formula.realize_not, Formula.realize_relabel] at h
  have hv : (![(e : ℕ)] ∘ (fun _ : Fin 2 => (0 : Fin 1))) = ![e, e] := by
    funext i; fin_cases i <;> simp
  rw [hv] at h
  tauto

/-- **Tarski's undefinability of truth, in terms of an arbitrary Gödel numbering.**

Fix any encoding `code` of the arithmetical formulas in one free variable by natural numbers.
Then no arithmetical formula `θ(x, y)` defines arithmetical truth, in the sense that the
sentence `θ(⌜p⌝, n)` (with numerals substituted for the variables) is true in the standard
model exactly when `p(n)` is. -/
theorem Tarski_undefinability_of_encoding (code : arith.Formula (Fin 1) → ℕ) :
    ¬ ∃ θ : arith.Formula (Fin 2),
        ∀ (p : arith.Formula (Fin 1)) (n : ℕ),
          ((Sentence.Realize ℕ (θ.subst ![numeral (code p), numeral n] : arith.Sentence)) ↔
            p.Realize (M := ℕ) ![n]) := by
  rintro ⟨θ, hθ⟩
  refine Tarski_undefinability ⟨θ, fun p => ⟨code p, fun n => ?_⟩⟩
  have h := hθ p n
  have hv : ∀ w : Empty → ℕ,
      (fun a : Fin 2 => Term.realize (M := ℕ) w (![numeral (code p), numeral n] a)) =
        ![code p, n] := by
    intro w; funext i; fin_cases i <;> simp
  rw [Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst, hv] at h
  exact h

/-- An explicit form of the diagonal argument: for every arithmetical formula `θ(x, y)` the
arithmetical formula `p(y) := ¬ θ(y, y)` is not among the "definable sets" enumerated by `θ`;
the index `e` itself always witnesses the failure. This shows the content of
`Frontier.Tarski_undefinability`: the missing set is itself arithmetically definable. -/
theorem diagonal_formula_not_enumerated (θ : arith.Formula (Fin 2)) :
    ∀ e : ℕ, ¬ ((θ.Realize (M := ℕ) ![e, e]) ↔
      Formula.Realize (M := ℕ) (∼ (θ.relabel (fun _ => 0))) ![e]) := by
  intro e h
  rw [Formula.realize_not, Formula.realize_relabel] at h
  have hv : (![(e : ℕ)] ∘ (fun _ : Fin 2 => (0 : Fin 1))) = ![e, e] := by
    funext i; fin_cases i <;> simp
  rw [hv] at h
  tauto

end Frontier

