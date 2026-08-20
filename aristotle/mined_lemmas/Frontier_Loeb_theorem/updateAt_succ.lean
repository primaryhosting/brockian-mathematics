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

theorem updateAt_succ (k v n : ℕ) (env : ℕ → ℕ) :
    updateAt (k + 1) v (push n env) = push n (updateAt k v env) := by
  funext i
  cases i <;> simp [updateAt, push]

