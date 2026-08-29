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
