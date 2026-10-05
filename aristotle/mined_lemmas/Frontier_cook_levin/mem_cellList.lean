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

theorem mem_cellList {n : Nat} (s : Cell n) : s ∈ cellList n := by
  obtain ⟨γ, h⟩ := s
  refine List.mem_flatMap.mpr ⟨γ, mem_symList γ, ?_⟩
  refine List.mem_map.mpr ⟨h, ?_, rfl⟩
  cases h with
  | none => simp
  | some q => exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange q))

/-- Width of the tableau: the number of tape cells that are tracked. -/
