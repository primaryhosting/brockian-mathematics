import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Arithmetical truth is not arithmetically definable (Tarski's undefinability theorem).

Everything is built from scratch: the syntax of first-order arithmetic (with named
variables), its satisfaction relation in the standard model `ℕ`, the notion of an
arithmetically definable set/relation, Gödel numberings, and the truth set.
-/

namespace Frontier

set_option autoImplicit false

/-! ## Syntax of first-order arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, *}`, with variables indexed by `ℕ`. -/
inductive ATerm : Type
  | var : ℕ → ATerm
  | zero : ATerm
  | succ : ATerm → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq, Encodable

/-- Formulas of the language of arithmetic.  `all i φ` is `∀ xᵢ, φ`. -/
inductive AForm : Type
  | eq : ATerm → ATerm → AForm
  | not : AForm → AForm
  | and : AForm → AForm → AForm
  | all : ℕ → AForm → AForm
  deriving DecidableEq, Encodable

instance : Inhabited AForm := ⟨AForm.eq ATerm.zero ATerm.zero⟩

/-- Evaluation of a term in the standard model `ℕ` under an assignment `ρ`. -/

theorem exists_goedel_numbering_with_undefinable_truth :
    ∃ (code : AForm → ℕ) (enum : ℕ → AForm) (diag : ℕ → AForm),
      Function.Injective code ∧ Function.Surjective enum ∧
      (∀ (e : ℕ) (ρ : ℕ → ℕ), Sat (diag e) ρ ↔ Sat (enum e) (Function.update ρ 0 e)) ∧
      (Definable2 fun x y => y = code (diag x)) ∧
      ¬ Definable1 (TruthSet code) := by
  have hdiagdef : Definable2 fun x y => y = stdCode (diagForm x) := by
    refine ⟨.eq (.var 1) (.succ (.add (.var 0) (.var 0))), fun ρ => ?_⟩
    simp only [Sat_eq, evalTerm, stdCode_diagForm]
    omega
  exact ⟨stdCode, formEnum, diagForm, stdCode_injective, formEnum_surjective, Sat_diagForm,
    hdiagdef,
    Tarski_undefinability stdCode stdCode_injective formEnum formEnum_surjective diagForm
      Sat_diagForm hdiagdef⟩

/-! ## Sanity checks: the framework is non-degenerate -/

/-- The set of even numbers is arithmetically definable, so `Definable1` is not empty. -/
