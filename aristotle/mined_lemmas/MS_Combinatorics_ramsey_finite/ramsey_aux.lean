import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

private lemma ramsey_aux : ∀ r s : ℕ, ∃ N : ℕ, ∀ (V : Type) [DecidableEq V]
    (f : Sym2 V → Bool) (S : Finset V), N ≤ S.card →
    (∃ A ⊆ S, r ≤ A.card ∧ MonoColor f true A) ∨
    (∃ B ⊆ S, s ≤ B.card ∧ MonoColor f false B) := by
  intro r
  induction r with
  | zero =>
      intro s
      refine ⟨0, fun V _ f S _ => Or.inl ⟨∅, Finset.empty_subset _, by simp, ?_⟩⟩
      intro x hx; simp at hx
  | succ r ihr =>
      intro s
      induction s with
      | zero =>
          refine ⟨0, fun V _ f S _ => Or.inr ⟨∅, Finset.empty_subset _, by simp, ?_⟩⟩
          intro x hx; simp at hx
      | succ s ihs =>
          obtain ⟨N1, h1⟩ := ihr (s + 1)
          obtain ⟨N2, h2⟩ := ihs
          refine ⟨N1 + N2 + 1, ?_⟩
          intro V _ f S hS
          -- pick a vertex `v` of `S`
          have hSne : S.Nonempty := by
            rw [← Finset.card_pos]; omega
          obtain ⟨v, hv⟩ := hSne
          set T := S.erase v with hT
          have hTcard : N1 + N2 ≤ T.card := by
            rw [hT, Finset.card_erase_of_mem hv]
            omega
          set R := T.filter (fun u => f s(v, u) = true) with hR
          set Bl := T.filter (fun u => f s(v, u) = false) with hBl
          have hsplit : R.card + Bl.card = T.card := by
            have hBl' : Bl = T.filter (fun u => ¬ (f s(v, u) = true)) := by
              rw [hBl]; apply Finset.filter_congr; intro x _; simp
            rw [hR, hBl', Finset.card_filter_add_card_filter_not]
          have hRT : R ⊆ T := Finset.filter_subset _ _
          have hBlT : Bl ⊆ T := Finset.filter_subset _ _
          have hTS : T ⊆ S := Finset.erase_subset _ _
          have hcase : N1 ≤ R.card ∨ N2 ≤ Bl.card := by omega
          rcases hcase with hc | hc
          · rcases h1 V f R hc with ⟨A, hAR, hAcard, hAmono⟩ | ⟨B, hBR, hBcard, hBmono⟩
            · -- extend `A` by `v`
              have hvA : v ∉ A := by
                intro hvA
                have := hAR hvA
                have : v ∈ T := hRT this
                exact (Finset.notMem_erase v S) this
              refine Or.inl ⟨insert v A, ?_, ?_, ?_⟩
              · intro x hx
                rcases Finset.mem_insert.1 hx with rfl | hx
                · exact hv
                · exact hTS (hRT (hAR hx))
              · rw [Finset.card_insert_of_notMem hvA]; omega
              · intro x hx y hy hxy
                rcases Finset.mem_insert.1 hx with rfl | hxA
                · rcases Finset.mem_insert.1 hy with rfl | hyA
                  · exact absurd rfl hxy
                  · exact (Finset.mem_filter.1 (hAR hyA)).2
                · rcases Finset.mem_insert.1 hy with rfl | hyA
                  · rw [Sym2.eq_swap]
                    exact (Finset.mem_filter.1 (hAR hxA)).2
                  · exact hAmono x hxA y hyA hxy
            · exact Or.inr ⟨B, fun x hx => hTS (hRT (hBR hx)), hBcard, hBmono⟩
          · rcases h2 V f Bl hc with ⟨A, hABl, hAcard, hAmono⟩ | ⟨B, hBBl, hBcard, hBmono⟩
            · exact Or.inl ⟨A, fun x hx => hTS (hBlT (hABl hx)), hAcard, hAmono⟩
            · have hvB : v ∉ B := by
                intro hvB
                exact (Finset.notMem_erase v S) (hBlT (hBBl hvB))
              refine Or.inr ⟨insert v B, ?_, ?_, ?_⟩
              · intro x hx
                rcases Finset.mem_insert.1 hx with rfl | hx
                · exact hv
                · exact hTS (hBlT (hBBl hx))
              · rw [Finset.card_insert_of_notMem hvB]; omega
              · intro x hx y hy hxy
                rcases Finset.mem_insert.1 hx with rfl | hxB
                · rcases Finset.mem_insert.1 hy with rfl | hyB
                  · exact absurd rfl hxy
                  · exact (Finset.mem_filter.1 (hBBl hyB)).2
                · rcases Finset.mem_insert.1 hy with rfl | hyB
                  · rw [Sym2.eq_swap]
                    exact (Finset.mem_filter.1 (hBBl hxB)).2
                  · exact hBmono x hxB y hyB hxy

