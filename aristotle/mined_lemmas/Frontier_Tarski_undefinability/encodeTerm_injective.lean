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
