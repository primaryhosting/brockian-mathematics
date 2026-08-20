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

def IsArithmetical₂ (R : Set (ℕ × ℕ)) : Prop :=
  ∃ φ : arith.Formula (Fin 2), ∀ v : Fin 2 → ℕ, (v 0, v 1) ∈ R ↔ φ.Realize v

/-! ## Gödel numberings and the satisfaction relation -/

/-- A *Gödel numbering* of the arithmetical formulas in one free variable is any surjection
from `ℕ` onto those formulas. (Formulas form a countable set, so such numberings exist; see
`exists_goedelNumbering`.) -/
