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

theorem Sat_shift_to_var_one {S : Set ℕ} {φ : AForm} (hφ : ∀ ρ : ℕ → ℕ, Sat φ ρ ↔ ρ 0 ∈ S)
    (ρ : ℕ → ℕ) :
    Sat (.all 0 (.not (.and (.eq (.var 0) (.var 1)) (.not φ)))) ρ ↔ ρ 1 ∈ S := by
  have key : ∀ w : ℕ, Sat φ (Function.update ρ 0 w) ↔ w ∈ S := by
    intro w; rw [hφ]; simp
  simp only [Sat_all, Sat_not, Sat_and, Sat_eq, evalTerm]
  constructor
  · intro h
    by_contra hmem
    exact h (ρ 1) ⟨by simp, fun hs => hmem ((key _).mp hs)⟩
  · rintro hmem w ⟨hw, hns⟩
    simp only [Function.update_self] at hw
    rw [show Function.update ρ 0 w 1 = ρ 1 by simp] at hw
    exact hns ((key w).mpr (hw ▸ hmem))

