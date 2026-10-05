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

theorem mem_cellClauses_atMostOne {n : Nat} (T Wd t i : Nat) (ht : t ≤ T) (hi : i < Wd)
    (s s' : Cell n) (hss : s ≠ s') :
    [(⟨(t, i, s), false⟩ : Lit (TVar n)), ⟨(t, i, s'), false⟩] ∈ cellClauses n T Wd :=
  List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨s, mem_cellList s,
        List.mem_filterMap.mpr ⟨s', mem_cellList s', by rw [if_neg hss]⟩⟩)⟩⟩

