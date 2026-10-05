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
