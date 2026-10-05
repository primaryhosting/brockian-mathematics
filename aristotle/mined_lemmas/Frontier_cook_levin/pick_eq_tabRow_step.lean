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

theorem pick_eq_tabRow_step {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (A : TVar n → Bool)
    (hcell : CNF.eval A (cellClauses n T (tabWidth T x m)) = true)
    (htrans : CNF.eval A (transClauses M T (tabWidth T x m)) = true)
    (t : Nat) (ht : t + 1 ≤ T)
    (ih : ∀ i, i < tabWidth T x m → pick A t i = tabRow M (x ++ pickWitness A x m) t i) :
    ∀ i, i < tabWidth T x m →
      pick A (t + 1) i = tabRow M (x ++ pickWitness A x m) (t + 1) i := by
  have hulen : (x ++ pickWitness A x m).length = x.length + m := by
    simp [pickWitness_length]
  have hWd : tabWidth T x m = x.length + m + T + 3 := rfl
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    have hb := pick_spec A T (tabWidth T x m) t 0 hcell (by omega) (by omega)
    have hd := pick_spec A T (tabWidth T x m) t 1 hcell (by omega) (by omega)
    have hcl := (CNF.eval_eq_true_iff _ _).mp htrans _
      (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
        List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨pick A t 0, mem_cellList _,
            List.mem_map_of_mem (mem_cellList (pick A t 1))⟩))⟩)
    have hres : A (t + 1, 0, M.ruleL (pick A t 0) (pick A t 1)) = true := by
      simpa [Clause.eval, Lit.eval, hb, hd] using hcl
    have hp := (pick_uniq A T (tabWidth T x m) (t + 1) 0 hcell ht (by omega) _ hres).symm
    rw [hp, ih 0 (by omega), ih 1 (by omega), tabRow_step_zero]
  · obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    by_cases hlast : i0 + 1 = tabWidth T x m - 1
    · -- rightmost column
      have hW2 : tabWidth T x m - 2 = x.length + m + T + 1 := by rw [hWd]; omega
      have hW1 : tabWidth T x m - 1 = x.length + m + T + 2 := by rw [hWd]; omega
      have ha := pick_spec A T (tabWidth T x m) t (tabWidth T x m - 2) hcell (by omega) (by omega)
      have hb := pick_spec A T (tabWidth T x m) t (tabWidth T x m - 1) hcell (by omega) (by omega)
      have hcl := (CNF.eval_eq_true_iff _ _).mp htrans _
        (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
          List.mem_append_right _
            (List.mem_flatMap.mpr ⟨pick A t (tabWidth T x m - 2), mem_cellList _,
              List.mem_map_of_mem (mem_cellList (pick A t (tabWidth T x m - 1)))⟩)⟩)
      have hres : A (t + 1, tabWidth T x m - 1,
          M.ruleR (pick A t (tabWidth T x m - 2)) (pick A t (tabWidth T x m - 1))) = true := by
        simpa [Clause.eval, Lit.eval, ha, hb] using hcl
      have hp := (pick_uniq A T (tabWidth T x m) (t + 1) (tabWidth T x m - 1) hcell ht
        (by omega) _ hres).symm
      have hfar : tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 3) =
          ((none : Sym), (none : Option (Fin n))) :=
        tabRow_far M (x ++ pickWitness A x m) t _ (by omega) (by omega)
      have hstep : tabRow M (x ++ pickWitness A x m) (t + 1) (x.length + m + T + 2) =
          M.rule (tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 1))
            (tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 2))
            (tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 3)) :=
        tabRow_step_interior M (x ++ pickWitness A x m) t (x.length + m + T + 1)
      rw [hlast, hp, ih _ (by omega), ih _ (by omega), hW1, hW2, hstep, hfar]
      rfl
    · -- interior column
      have hi0 : i0 < tabWidth T x m - 2 := by omega
      have ha := pick_spec A T (tabWidth T x m) t i0 hcell (by omega) (by omega)
      have hb := pick_spec A T (tabWidth T x m) t (i0 + 1) hcell (by omega) (by omega)
      have hd := pick_spec A T (tabWidth T x m) t (i0 + 2) hcell (by omega) (by omega)
      have hcl := (CNF.eval_eq_true_iff _ _).mp htrans _
        (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
          List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨i0, List.mem_range.mpr hi0,
              List.mem_flatMap.mpr ⟨pick A t i0, mem_cellList _,
                List.mem_flatMap.mpr ⟨pick A t (i0 + 1), mem_cellList _,
                  List.mem_map_of_mem (mem_cellList (pick A t (i0 + 2)))⟩⟩⟩))⟩)
      have hres : A (t + 1, i0 + 1,
          M.rule (pick A t i0) (pick A t (i0 + 1)) (pick A t (i0 + 2))) = true := by
        simpa [Clause.eval, Lit.eval, ha, hb, hd] using hcl
      have hp := (pick_uniq A T (tabWidth T x m) (t + 1) (i0 + 1) hcell ht (by omega) _ hres).symm
      rw [hp, ih i0 (by omega), ih (i0 + 1) (by omega), ih (i0 + 2) (by omega),
        tabRow_step_interior]

