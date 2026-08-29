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

theorem Definable1.preimage {S : Set ℕ} {f : ℕ → ℕ} (hS : Definable1 S)
    (hf : Definable2 fun x y => y = f x) : Definable1 (f ⁻¹' S) := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨θ, hθ⟩ := hf
  -- `∀ x₁, θ(x₀,x₁) → (∀ x₀, x₀ = x₁ → φ(x₀))`
  refine ⟨.all 1 (.not (.and θ (.not (.all 0 (.not (.and (.eq (.var 0) (.var 1)) (.not φ))))))), ?_⟩
  intro ρ
  have hin : ∀ v : ℕ, Sat (.all 0 (.not (.and (.eq (.var 0) (.var 1)) (.not φ))))
      (Function.update ρ 1 v) ↔ v ∈ S := by
    intro v
    rw [Sat_shift_to_var_one hφ]
    simp
  have hth : ∀ v : ℕ, Sat θ (Function.update ρ 1 v) ↔ v = f (ρ 0) := by
    intro v
    rw [hθ]
    simp
  simp only [Sat_all, Sat_not, Sat_and, Set.mem_preimage]
  constructor
  · intro h
    by_contra hmem
    exact h (f (ρ 0)) ⟨(hth _).mpr rfl, fun hs => hmem ((hin _).mp hs)⟩
  · rintro hmem v ⟨hv, hns⟩
    exact hns ((hin v).mpr (((hth v).mp hv) ▸ hmem))

/-- The diagonal of a definable binary relation is definable. -/
