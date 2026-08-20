/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with function symbols `0, 1, +, *`
and no relation symbols. -/

theorem exists_goedelNumbering : ∃ num : ℕ → arith.Formula (Fin 1), IsGoedelNumbering num :=
  exists_surjective_nat _

/-- *Arithmetical truth*, relative to a Gödel numbering `num`: the set of pairs `(e, n)` such
that the formula with code `e` is true in the standard model `ℕ` of the number `n`.
This is Tarski's satisfaction relation for the language of arithmetic. -/
