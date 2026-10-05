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
