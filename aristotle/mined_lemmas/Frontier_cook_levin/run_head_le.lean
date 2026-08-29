/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no `import`, so that the module
docstring above can literally be the first thing in the file).  The definitions of `Lit`,
`Clause`, `CNF`, `Clause.eval` and `CNF.eval` below mirror `Std.Sat.Literal`,
`Std.Sat.CNF.Clause`, `Std.Sat.CNF`, `Std.Sat.CNF.Clause.eval` and `Std.Sat.CNF.eval`
from the Lean standard library.
-/

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal: a variable together with the sign with which it occurs. -/
abbrev Lit (V : Type) := V × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a clause under an assignment. -/

theorem run_head_le (hrun : M.Run x T c) : ∀ t, t ≤ T → (c t).head ≤ t := by
  intro t
  induction t with
  | zero => intro _; rw [hrun.1]; simp [NTM.init]
  | succ t ih =>
    intro ht
    obtain ⟨p, -, -, -, h3⟩ := hrun.2 t (by omega)
    have h4 := Move.apply_le p.2.2 (c t).head
    have h5 := ih (by omega)
    rw [h3]
    omega

