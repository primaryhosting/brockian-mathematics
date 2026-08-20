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

set_option grind.warning false

/-!
# Tarski's undefinability of truth

This file formalizes Tarski's theorem: *arithmetical truth is not arithmetically definable*.

We work with the first-order language of arithmetic `Frontier.arith`, with signature
`(0, 1, +, *)`, interpreted in its standard model `ℕ`.

* A set `S ⊆ ℕ` is **arithmetical** (`Frontier.Arithmetical`) if there is a formula `phi(x)` of
  the language of arithmetic, with one free variable, such that `n ∈ S ↔ ℕ ⊨ phi(n)`.
  Similarly for binary relations (`Frontier.Arithmetical₂`).

* Fix any enumeration `f : ℕ → arith.Formula (Fin 1)` of the formulas with one free variable
  (such enumerations exist, since the language is countable: see
  `Frontier.exists_surjective_enumeration`). The **arithmetical truth relation** relative to
  this enumeration is
  `Frontier.truthSet f = {(e, n) | ℕ ⊨ (f e)(n)}`,
  i.e. the satisfaction relation "the `e`-th formula is true of `n`".

The theorem `Frontier.Tarski_undefinability` states that, for *every* enumeration `f` of the
formulas, the truth relation `truthSet f` is **not** arithmetical: no single arithmetical
formula `psi(x, y)` can express "the formula with code `x` is true of `y`". This is the standard
coding-free (semantic) form of Tarski's undefinability theorem, and it is proved by
diagonalization.
-/

namespace Frontier

open FirstOrder Language Function

/-- The function symbols of the language of arithmetic: the constants `0` and `1`, and the
binary operations `+` and `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with signature `(0, 1, +, *)` and no relation
symbols. -/

theorem Tarski_undefinability (f : ℕ → arith.Formula (Fin 1)) (hf : Surjective f) :
    ¬ Arithmetical₂ (truthSet f) := by
  rintro ⟨psi, hpsi⟩
  -- The diagonal set is defined by the formula `¬ psi(x, x)`, contradicting `diagonal_not_arithmetical`.
  refine diagonal_not_arithmetical f hf ⟨(Formula.relabel (fun _ => 0) psi).not, fun n => ?_⟩
  have hcomp : (![n] : Fin 1 → ℕ) ∘ (fun _ : Fin 2 => (0 : Fin 1)) = ![n, n] := by
    funext i; fin_cases i <;> rfl
  rw [Set.mem_setOf_eq, Formula.realize_not, Formula.realize_relabel, hcomp]
  exact not_congr (hpsi n n)

/-! ### Sanity checks: the notion of an arithmetical set is not degenerate. -/

/-- The set of idempotent naturals is arithmetical, being defined by `x * x = x`. -/
example : Arithmetical {n : ℕ | n * n = n} :=
  ⟨Term.equal (Functions.apply₂ arithFunc.mul (Term.var 0) (Term.var 0)) (Term.var 0), by
    intro n; simp [Formula.Realize, Term.equal, Term.realize, Structure.funMap]⟩

/-- The set of even naturals is arithmetical, being defined by `∃ y, x = y + y`. -/
example : Arithmetical {n : ℕ | ∃ m, n = m + m} :=
  ⟨BoundedFormula.ex (Term.bdEqual (Term.var (Sum.inl 0))
      (Functions.apply₂ arithFunc.add (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0)))), by
    intro n
    simp [Formula.Realize, Term.realize, Structure.funMap, Fin.snoc]⟩

end Frontier

