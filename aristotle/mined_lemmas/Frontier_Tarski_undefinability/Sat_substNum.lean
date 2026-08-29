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

theorem Sat_substNum (i k : ℕ) (φ : AForm) (ρ : ℕ → ℕ) :
    Sat (substNum i k φ) ρ ↔ Sat φ (Function.update ρ i k) := by
  induction φ generalizing ρ with
  | eq s t => simp [substNum, evalTerm_substTermNum]
  | not φ ih => simp [substNum, ih]
  | and φ ψ ihφ ihψ => simp [substNum, ihφ, ihψ]
  | all j φ ih =>
    by_cases h : j = i
    · subst h
      have hsub : substNum j k (AForm.all j φ) = AForm.all j φ := by simp [substNum]
      rw [hsub]
      simp only [Sat_all]
      exact forall_congr' fun v => by rw [Function.update_idem]
    · simp only [substNum, if_neg h, Sat_all]
      exact forall_congr' fun v => by rw [ih, Function.update_comm h]

/-! ## Definability in the standard model -/

/-- A set `S ⊆ ℕ` is *arithmetically definable* if some formula of arithmetic defines it,
using `x₀` as its (only) free variable. -/
