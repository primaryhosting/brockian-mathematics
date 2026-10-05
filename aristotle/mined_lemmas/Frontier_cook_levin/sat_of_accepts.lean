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

theorem sat_of_accepts {M : NTM} {T : Nat} {x : List Bool} (h : M.AcceptsWithin x T) :
    Satisfiable (tableau M T x) := by
  obtain ⟨c, hrun, t0, ht0, hacc⟩ := h
  have hex : ∀ t : Nat, ∃ τ : Trans, t < T → StepData M c t τ := by
    intro t
    by_cases ht : t < T
    · obtain ⟨p, hp, h1, h2, h3⟩ := hrun.2 t ht
      exact ⟨((c t).state, (c t).tape (c t).head, p.1, p.2.1, p.2.2),
        fun _ => ⟨rfl, rfl, hp, h1, h2, h3⟩⟩
    · exact ⟨(0, none, 0, none, Move.stay), fun h' => absurd h' ht⟩
  obtain ⟨tr, htr⟩ := Classical.axiomOfChoice hex
  refine ⟨assignOf c tr, ?_⟩
  rw [cnf_eval_iff]
  intro cl hcl
  simp only [tableau, List.mem_append] at hcl
  rcases hcl with h | h | h | h | h | h | h | h | h | h | h
  · exact sat_stateOne hrun cl h
  · exact sat_stateAtMostOne cl h
  · exact sat_headOne hrun cl h
  · exact sat_headAtMostOne cl h
  · exact sat_cellOne cl h
  · exact sat_cellAtMostOne cl h
  · exact sat_initClauses hrun cl h
  · exact sat_acceptClause ht0 hacc cl h
  · exact sat_transOne hrun htr cl h
  · exact sat_transImp htr cl h
  · exact sat_frameClauses htr cl h

/-- **Correctness of the Cook–Levin tableau encoding**: the CNF formula `tableau M T x` is
satisfiable if and only if the nondeterministic machine `M` accepts the input `x` within
`T` steps. -/
