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

theorem mem_cellClauses_atLeastOne {n : Nat} (T Wd t i : Nat) (ht : t ≤ T) (hi : i < Wd) :
    ((cellList n).map fun s => (⟨(t, i, s), true⟩ : Lit (TVar n))) ∈ cellClauses n T Wd :=
  List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_cons_self⟩⟩

