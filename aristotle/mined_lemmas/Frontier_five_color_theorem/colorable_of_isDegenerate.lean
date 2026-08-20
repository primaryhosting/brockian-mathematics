import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem colorable_of_isDegenerate (k : ℕ) (H : IsDegenerate G k) : G.Colorable (k + 1) := by
  classical
  have main : ∀ n : ℕ, ∀ s : Finset V, s.card = n →
      ∃ c : V → Fin (k + 1), ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → c a ≠ c b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨fun _ => 0, by simp⟩
      obtain ⟨v, hv, hvdeg⟩ := H s hne
      have hlt : (s.erase v).card < n := by
        rw [Finset.card_erase_of_mem hv, ← hs]
        exact Nat.sub_lt (Finset.card_pos.mpr hne) one_pos
      obtain ⟨c, hc⟩ := ih (s.erase v).card hlt (s.erase v) rfl
      set T : Finset (Fin (k + 1)) := ((s.erase v).filter (fun w => G.Adj v w)).image c
      have hT : T.card ≤ k := le_trans Finset.card_image_le hvdeg
      have hex : ∃ x : Fin (k + 1), x ∉ T := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ T := fun x _ => hcon x
        have := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨x, hx⟩ := hex
      refine ⟨Function.update c v x, ?_⟩
      intro a ha b hb hab
      have hmemT : ∀ w ∈ s, w ≠ v → G.Adj v w → c w ∈ T := by
        intro w hw hwv hadj
        exact Finset.mem_image_of_mem c
          (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwv, hw⟩, hadj⟩)
      by_cases hav : a = v
      · subst hav
        have hba : b ≠ a := (G.ne_of_adj hab).symm
        rw [Function.update_self, Function.update_of_ne hba]
        exact fun hcontra => hx (hcontra ▸ hmemT b hb hba hab)
      · by_cases hbv : b = v
        · subst hbv
          rw [Function.update_self, Function.update_of_ne hav]
          exact fun hcontra =>
            hx (hcontra.symm ▸ hmemT a ha hav (G.symm hab))
        · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
          exact hc a (Finset.mem_erase.mpr ⟨hav, ha⟩) b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
  obtain ⟨c, hc⟩ := main (Finset.univ : Finset V).card Finset.univ rfl
  exact ⟨SimpleGraph.Coloring.mk c fun {a b} hab =>
    hc a (Finset.mem_univ a) b (Finset.mem_univ b) hab⟩

/-- A graph is *hereditarily planar* if all of its induced subgraphs are planar in the sense of
`Frontier.IsPlanar`. Mathematically this is equivalent to planarity of `G` itself, since an
induced subgraph of a planar graph is planar; that implication involves surgery on rotation
systems and is not formalised here, so the theorems below take it as a hypothesis. -/
