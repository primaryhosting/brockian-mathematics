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

theorem Provable_consistent : ¬ (⊢ Fml.bot) := fun h => soundness h (fun _ => 0)

end Frontier

import Mathlib

/-!
# Löb's theorem for Peano Arithmetic

This file contains a self-contained formalization of the syntax of first-order arithmetic,
of a Hilbert-style proof calculus for Peano Arithmetic (`Frontier.Provable`), and a proof of
**Löb's theorem**: if `PA ⊢ □φ → φ` then `PA ⊢ φ`, where `□` is any operation on formulas
satisfying the Hilbert–Bernays–Löb derivability conditions together with the Gödel diagonal
(fixed point) property.  The intended instance of `□` is `fun φ => Prov(⌜φ⌝)`, the arithmetized
provability predicate of `PA` applied to the numeral of the Gödel number of `φ`; the derivability
conditions and the diagonal lemma for that particular `□` are the standard arithmetization
facts and are taken here as explicit hypotheses of the theorem (they are *not* axioms: the
