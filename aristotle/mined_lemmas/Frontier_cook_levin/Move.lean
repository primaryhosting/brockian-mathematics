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

theorem Move.apply_le (d : Move) (i : Nat) : d.apply i ≤ i + 1 := by
  cases d <;> simp [Move.apply] <;> omega

/-- A nondeterministic Turing machine with tape alphabet `Sym = Option Bool` and
state set `{0, ..., numStates - 1}`.  `step q a` lists the possible successor triples
(new state, symbol written, head movement). -/
structure NTM where
  numStates : Nat
  start : Nat
  accept : Nat
  step : Nat → Sym → List (Nat × Sym × Move)
  start_lt : start < numStates
  accept_lt : accept < numStates
  step_lt : ∀ q a p, p ∈ step q a → p.1 < numStates
  step_ne : ∀ q a, step q a ≠ []

/-- A configuration: current state, tape contents, head position. -/
structure Cfg where
  state : Nat
  tape : Nat → Sym
  head : Nat

/-- Update a tape at one position. -/
