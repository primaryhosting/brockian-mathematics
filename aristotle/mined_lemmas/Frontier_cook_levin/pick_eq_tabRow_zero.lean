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

theorem pick_eq_tabRow_zero {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (A : TVar n → Bool)
    (hcell : CNF.eval A (cellClauses n T (tabWidth T x m)) = true)
    (hinit : CNF.eval A (initClauses M T x m) = true) :
    ∀ i, i < tabWidth T x m → pick A 0 i = tabRow M (x ++ pickWitness A x m) 0 i := by
  have hulen : (x ++ pickWitness A x m).length = x.length + m := by
    simp [pickWitness_length]
  intro i hi
  rw [tabRow_zero]
  by_cases h0 : i = 0
  · subst h0
    have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _ (List.mem_cons_self)
    rw [Clause.eval_eq_true_iff] at hcl
    obtain ⟨l, hl, hlv⟩ := hcl
    rw [List.mem_singleton] at hl
    subst hl
    have hAv : A (0, 0, ((none : Sym), some M.start)) = true := by simpa [Lit.eval] using hlv
    rw [M.cell_initCfg_zero]
    exact (pick_uniq A T (tabWidth T x m) 0 0 hcell (by omega) hi _ hAv).symm
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [M.cell_initCfg_succ]
    by_cases h1 : j < x.length
    · have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map_of_mem (List.mem_range.mpr h1)))))
      rw [Clause.eval_eq_true_iff] at hcl
      obtain ⟨l, hl, hlv⟩ := hcl
      rw [List.mem_singleton] at hl
      subst hl
      have hAv : A (0, j + 1, (some (x.getD j false), (none : Option (Fin n)))) = true := by
        simpa [Lit.eval] using hlv
      have hval : (x ++ pickWitness A x m)[j]? = some (x.getD j false) := by
        rw [List.getElem?_append_left h1]
        simp [List.getD, List.getElem?_eq_getElem h1]
      rw [hval]
      exact (pick_uniq A T (tabWidth T x m) 0 (j + 1) hcell (by omega) hi _ hAv).symm
    · by_cases h2 : j < x.length + m
      · obtain ⟨jj, rfl⟩ : ∃ jj, j = x.length + jj := ⟨j - x.length, by omega⟩
        have hjj : jj < m := by omega
        have hidx : x.length + jj + 1 = x.length + 1 + jj := by omega
        have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map_of_mem (List.mem_range.mpr hjj)))))
        rw [Clause.eval_eq_true_iff] at hcl
        obtain ⟨l, hl, hlv⟩ := hcl
        have hpick : ∃ b : Bool, pick A 0 (x.length + 1 + jj) = (some b, (none : Option (Fin n))) := by
          rcases List.mem_cons.mp hl with rfl | hl
          · refine ⟨false, ?_⟩
            have hAv : A (0, x.length + 1 + jj, (some false, (none : Option (Fin n)))) = true := by
              simpa [Lit.eval] using hlv
            exact (pick_uniq A T (tabWidth T x m) 0 (x.length + 1 + jj) hcell (by omega)
              (by omega) _ hAv).symm
          · rcases List.mem_cons.mp hl with rfl | hl
            · refine ⟨true, ?_⟩
              have hAv : A (0, x.length + 1 + jj, (some true, (none : Option (Fin n)))) = true := by
                simpa [Lit.eval] using hlv
              exact (pick_uniq A T (tabWidth T x m) 0 (x.length + 1 + jj) hcell (by omega)
                (by omega) _ hAv).symm
            · simp at hl
        obtain ⟨b, hb⟩ := hpick
        have hbit : (pickWitness A x m).getD jj false = b := by
          rw [pickWitness_getD A x m jj hjj, hb]
          rfl
        have hval : (x ++ pickWitness A x m)[x.length + jj]? = some b := by
          rw [List.getElem?_append_right (by omega)]
          have hjj' : jj < (pickWitness A x m).length := by rw [pickWitness_length]; exact hjj
          have : x.length + jj - x.length = jj := by omega
          rw [this, List.getElem?_eq_getElem hjj']
          have : (pickWitness A x m)[jj] = (pickWitness A x m).getD jj false := by
            rw [List.getD, List.getElem?_eq_getElem hjj']
            rfl
          rw [this, hbit]
        rw [hval, hidx, hb]
      · obtain ⟨jj, rfl⟩ : ∃ jj, j = x.length + m + jj := ⟨j - (x.length + m), by omega⟩
        have hjj : jj < T + 2 := by
          simp only [tabWidth] at hi
          omega
        have hidx : x.length + m + jj + 1 = x.length + m + 1 + jj := by omega
        have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _
          (List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_map_of_mem (List.mem_range.mpr hjj))))
        rw [Clause.eval_eq_true_iff] at hcl
        obtain ⟨l, hl, hlv⟩ := hcl
        rw [List.mem_singleton] at hl
        subst hl
        have hAv : A (0, x.length + m + 1 + jj, ((none : Sym), (none : Option (Fin n)))) = true := by
          simpa [Lit.eval] using hlv
        have hval : (x ++ pickWitness A x m)[x.length + m + jj]? = none :=
          List.getElem?_eq_none (by omega)
        rw [hval, hidx]
        exact (pick_uniq A T (tabWidth T x m) 0 (x.length + m + 1 + jj) hcell (by omega)
          (by omega) _ hAv).symm

