/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal over a type `V` of variables: a variable together with a polarity. -/
structure Lit (V : Type) where
  var : V
  pol : Bool
deriving DecidableEq

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a literal under an assignment. -/

theorem pick_uniq {n : Nat} (A : TVar n → Bool) (T Wd t i : Nat)
    (hcell : CNF.eval A (cellClauses n T Wd) = true) (ht : t ≤ T) (hi : i < Wd)
    (s : Cell n) (hs : A (t, i, s) = true) : s = pick A t i := by
  refine Classical.byContradiction fun hne => ?_
  have hcl := (CNF.eval_eq_true_iff _ _).mp hcell _
    (mem_cellClauses_atMostOne T Wd t i ht hi s (pick A t i) hne)
  rw [Clause.eval_eq_true_iff] at hcl
  obtain ⟨l, hl, hlv⟩ := hcl
  have hp := pick_spec A T Wd t i hcell ht hi
  rcases List.mem_cons.mp hl with rfl | hl
  · simp [Lit.eval, hs] at hlv
  · rcases List.mem_cons.mp hl with rfl | hl
    · simp [Lit.eval, hp] at hlv
    · simp at hl

/-- The witness read off from the initial row of an assignment. -/
