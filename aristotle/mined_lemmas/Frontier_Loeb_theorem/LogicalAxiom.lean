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

theorem LogicalAxiom.sat {φ : Fml} (h : LogicalAxiom φ) (env : ℕ → ℕ) : φ.Sat env := by
  induction h with
  | taut h => exact h.sat env
  | allElim φ t =>
    intro h
    rw [Fml.sat_inst]
    exact h _
  | allImp φ ψ => exact fun h hφ n => h n (hφ n)
  | eqRefl => intro n; rfl
  | eqSucc => intro n m h; simp [Fml.Sat, Trm.eval, push] at h ⊢; omega
  | eqAdd => intro a b c d; simp [Fml.Sat, Trm.eval, push]; omega
  | eqMul =>
    intro a b c d
    simp only [Fml.Sat, Trm.eval, push]
    intro h1 h2
    subst h1; subst h2; rfl
  | eqCongr => intro a b c d; simp [Fml.Sat, Trm.eval, push]; omega

