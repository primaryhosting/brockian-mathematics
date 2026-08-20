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

theorem no_universal_arithmetical_relation :
    ¬ ∃ U : Set (ℕ × ℕ), IsArithmetical₂ U ∧
      ∀ S : Set ℕ, IsArithmetical S → ∃ a : ℕ, S = {n | (a, n) ∈ U} := by
  rintro ⟨U, hU, huniv⟩
  obtain ⟨a, ha⟩ := huniv _ (isArithmetical_compl_diagonal hU)
  have : (a, a) ∉ U ↔ (a, a) ∈ U := by
    constructor
    · intro h; exact (Set.ext_iff.1 ha a).1 h
    · intro h hc; exact hc h
  tauto

/-- **Tarski's undefinability theorem.**  Arithmetical truth is not arithmetically definable:
for *any* Gödel numbering `num` of the formulas of arithmetic in one free variable, the
satisfaction relation `{(e, n) | ℕ ⊨ (num e)(n)}` is not definable by a formula of arithmetic
in the standard model `ℕ`. -/
