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

theorem stdCode_injective : Function.Injective stdCode := by
  intro φ ψ h
  rw [stdCode, stdCode] at h
  by_cases hφ : ∃ e, diagForm e = φ <;> by_cases hψ : ∃ e, diagForm e = ψ
  · rw [dif_pos hφ, dif_pos hψ] at h
    have : hφ.choose = hψ.choose := by omega
    rw [← hφ.choose_spec, ← hψ.choose_spec, this]
  · rw [dif_pos hφ, dif_neg hψ] at h
    omega
  · rw [dif_neg hφ, dif_pos hψ] at h
    omega
  · rw [dif_neg hφ, dif_neg hψ] at h
    exact Encodable.encode_injective (by omega)

/-- There exists a Gödel numbering satisfying all the hypotheses of
`Tarski_undefinability`; in particular, the theorem is not vacuous. -/
