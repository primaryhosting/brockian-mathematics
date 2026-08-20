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

def propEval (v : Fml → Bool) : Fml → Bool
  | .eq t u => v (.eq t u)
  | .bot => false
  | .imp a b => !(propEval v a) || propEval v b
  | .all a => v (.all a)

/-- A formula is a (propositional) tautology if it evaluates to `true` under every boolean
assignment to its prime subformulas.  Equivalently, it is a substitution instance of a
tautology of propositional logic. -/
