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

theorem no_universal_definable_relation (R : ℕ → ℕ → Prop) (hR : Definable2 R)
    (huniv : ∀ S : Set ℕ, Definable1 S → ∃ e : ℕ, ∀ m : ℕ, m ∈ S ↔ R e m) : False := by
  obtain ⟨e, he⟩ := huniv {n | R n n}ᶜ hR.diagonal.compl
  have := he e
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at this
  tauto

/-- **Tarski's undefinability theorem.**  Fix any Gödel numbering `code` of the formulas of
arithmetic (an injection into `ℕ`), any enumeration `enum` of the formulas, and diagonal
formulas `diag e` expressing "the `e`-th formula holds of `e`".  If the diagonal function
`e ↦ code (diag e)` is arithmetically definable — as it is for every standard, effective
Gödel numbering — then the set of Gödel numbers of the *true* formulas of arithmetic is not
arithmetically definable.  In short: arithmetical truth is not arithmetically definable. -/
