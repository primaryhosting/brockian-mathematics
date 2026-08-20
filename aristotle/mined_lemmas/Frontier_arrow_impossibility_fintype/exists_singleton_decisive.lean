/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem exists_singleton_decisive {F : (V → Ranking) → Ranking} (hU : Unanimous F)
    (hIIA : IIA F) :
    ∀ (n : Nat) (S : List V), S.length ≤ n → (∀ z w : Fin 3, z ≠ w → Decisive F S z w) →
      ∃ v, v ∈ S ∧ ∀ z w : Fin 3, z ≠ w → Decisive F [v] z w := by
  intro n
  induction n with
  | zero =>
    intro S hlen hdec
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hS
    exact absurd hdec (fun h => not_decisive_nil h)
  | succ n ih =>
    intro S hlen hdec
    match S with
    | [] => exact absurd hdec (fun h => not_decisive_nil h)
    | v :: rest =>
      by_cases hv : v ∈ rest
      · -- `v` is redundant: pass to the shorter list `rest`
        have hdec' : ∀ z w : Fin 3, z ≠ w → Decisive F rest z w := by
          intro z w hzw q hq
          refine hdec z w hzw q ?_
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hq u hv
          · exact hq u hu
        obtain ⟨v', hv', hd⟩ := ih rest (Nat.le_of_succ_le_succ hlen) hdec'
        exact ⟨v', List.mem_cons_of_mem _ hv', hd⟩
      · have hdisj : ∀ u, u ∈ [v] → u ∉ rest := by
          intro u hu
          rcases List.mem_singleton.mp hu with rfl
          exact hv
        have hdec01 : Decisive F ([v] ++ rest) 0 1 := by
          simpa using hdec 0 1 (by decide)
        rcases split_semiDecisive hIIA hdisj hdec01 with ⟨x, y, hxy, hSD⟩ | ⟨x, y, hxy, hSD⟩
        · exact ⟨v, List.mem_cons_self .., allDecisive_of_semiDecisive hU hIIA hxy hSD⟩
        · obtain ⟨v', hv', hd⟩ :=
            ih rest (Nat.le_of_succ_le_succ hlen)
              (allDecisive_of_semiDecisive hU hIIA hxy hSD)
          exact ⟨v', List.mem_cons_of_mem _ hv', hd⟩

/-! ## Arrow's impossibility theorem -/

/-- **Arrow's impossibility theorem** (base case: three alternatives, finitely many voters).

There is no social welfare function on finitely many voters (finiteness is expressed by a
list `L` of voters containing everyone) that aggregates strict rankings of three
alternatives, is unanimous (Pareto), satisfies independence of irrelevant alternatives, and
has no dictator. -/
