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

theorem propEval_eq_decide (env : ℕ → ℕ) (φ : Fml) :
    propEval (fun ψ => decide (ψ.Sat env)) φ = decide (φ.Sat env) := by
  induction φ with
  | eq t u => rfl
  | bot => simp [propEval, Fml.Sat]
  | imp a b iha ihb =>
    simp only [propEval, iha, ihb, Fml.Sat]
    by_cases ha : a.Sat env <;> by_cases hb : b.Sat env <;> simp [ha, hb]
  | all a => rfl

open Classical in
