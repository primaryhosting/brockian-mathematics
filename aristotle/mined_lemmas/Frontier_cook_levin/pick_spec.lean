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

theorem pick_spec {p : Nat → Bool} : ∀ {n : Nat}, (∃ q, q < n ∧ p q = true) →
    pick p n < n ∧ p (pick p n) = true := by
  intro n
  induction n with
  | zero => intro h; obtain ⟨q, hq, -⟩ := h; omega
  | succ n ih =>
    intro h
    by_cases hp : p n = true
    · refine ⟨?_, ?_⟩ <;> simp [pick, hp]
    · obtain ⟨q, hq, hpq⟩ := h
      have hq' : q < n := by
        have : q < n ∨ q = n := by omega
        rcases this with h' | h'
        · exact h'
        · exact absurd (h' ▸ hpq) hp
      have hrec := ih ⟨q, hq', hpq⟩
      have hpk : pick p (n + 1) = pick p n := by simp [pick, hp]
      rw [hpk]
      exact ⟨by omega, hrec.2⟩

/-- The state read off an assignment. -/
