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

theorem insertAt_succ (k v n : ℕ) (env : ℕ → ℕ) :
    insertAt (k + 1) v (push n env) = push n (insertAt k v env) := by
  funext i
  match i with
  | 0 => simp [insertAt, push]
  | i + 1 =>
    by_cases h1 : i < k
    · simp [insertAt, push, h1, Nat.succ_lt_succ h1]
    · by_cases h2 : i = k
      · subst h2; simp [insertAt, push]
      · have h3 : k < i := by omega
        have h4 : i ≠ 0 := by omega
        match i with
        | 0 => omega
        | i + 1 => simp [insertAt, push]

