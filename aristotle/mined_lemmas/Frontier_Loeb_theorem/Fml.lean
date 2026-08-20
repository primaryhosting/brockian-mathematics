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

def Fml.inst (φ : Fml) (t : Trm) : Fml := φ.subst 0 t

/-! ## Propositional tautologies -/

/-- Evaluation of a formula under a boolean assignment `v` to the *prime* formulas
(atomic formulas and universally quantified formulas), treating `⊥` and `→` as the
classical boolean connectives. -/
