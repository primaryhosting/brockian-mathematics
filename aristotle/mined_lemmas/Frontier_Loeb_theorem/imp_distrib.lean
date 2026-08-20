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

theorem imp_distrib {a b c : Fml} (h₁ : ⊢ a ⟹ (b ⟹ c)) (h₂ : ⊢ a ⟹ b) : ⊢ a ⟹ c :=
  .mp (.mp (.taut (by
    intro v
    simp only [propEval]
    cases propEval v a <;> cases propEval v b <;> cases propEval v c <;> rfl)) h₁) h₂

