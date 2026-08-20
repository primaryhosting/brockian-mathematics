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

def Trm.substK : Trm → ℕ → Trm → Trm
  | .var n, k, s => if n = k then s else .var n
  | .zero, _, _ => .zero
  | .succ t, k, s => .succ (t.substK k s)
  | .add t u, k, s => .add (t.substK k s) (u.substK k s)
  | .mul t u, k, s => .mul (t.substK k s) (u.substK k s)

/-- Substitute the term `s` for the variable `k` in a formula, without renaming the other
variables. -/
