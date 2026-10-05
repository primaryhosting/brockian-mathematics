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
