import RequestProject.Loeb

/-!
# Soundness and consistency of the calculus

We interpret the language of arithmetic in the standard model `ℕ` and prove that every formula
provable in `Frontier.Provable` is true in `ℕ` under every assignment.  In particular the
calculus is consistent (`Frontier.Provable_consistent`), so the formalization of Peano
Arithmetic used for Löb's theorem is not degenerate.
-/

namespace Frontier

/-! ## The standard model -/

/-- Extend an assignment by a value for the variable bound by the outermost `∀`. -/

theorem soundness {φ : Fml} (h : ⊢ φ) : ∀ env : ℕ → ℕ, φ.Sat env := by
  induction h with
  | logic h => exact h.sat
  | ax h => exact h.sat
  | mp _ _ ih₁ ih₂ => exact fun env => ih₁ env (ih₂ env)
  | gen _ ih => exact fun env n => ih (push n env)

/-- The calculus is consistent: `⊥` is not provable. -/
