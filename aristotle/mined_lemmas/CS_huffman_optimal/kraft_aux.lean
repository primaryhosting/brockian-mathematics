import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

private lemma kraft_aux : ∀ (n : ℕ) (L : List (List Bool)),
    (L.map List.length).sum ≤ n → PFList L → kraftSum L ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro L hlen hpf
      by_cases hm : [] ∈ L
      · rw [hpf.eq_singleton_nil hm]; simp [kraftSum]
      · have : L = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro a ha
          have hle : a.length ≤ (L.map List.length).sum :=
            List.le_sum_of_mem (List.mem_map_of_mem ha)
          have ha0 : a = [] := List.length_eq_zero_iff.mp (by omega)
          exact hm (ha0 ▸ ha)
        simp [this]
  | succ n ih =>
      intro L hlen hpf
      by_cases hm : [] ∈ L
      · rw [hpf.eq_singleton_nil hm]; simp [kraftSum]
      · have hne : ∀ x ∈ L, x ≠ [] := by
          intro x hx hx0; exact hm (hx0 ▸ hx)
        -- split according to the first bit
        have key : ∀ (p : List Bool → Bool),
            (∀ x ∈ L.filter p, ∀ y ∈ L.filter p, x.headI = y.headI) →
            kraftSum (L.filter p) ≤ (2 : ℝ)⁻¹ := by
          intro p hp
          set M := L.filter p with hM
          have hMsub : ∀ x ∈ M, x ∈ L := by
            intro x hx; exact List.mem_of_mem_filter hx
          have hMne : ∀ x ∈ M, x ≠ [] := fun x hx => hne x (hMsub x hx)
          have hMpf : PFList M := List.Pairwise.filter _ hpf
          rw [kraft_half M hMne]
          clear_value M
          have hsub : kraftSum (M.map List.tail) ≤ 1 := by
            rcases eq_or_ne M [] with hnil | hnil
            · simp [hnil]
            · refine ih _ ?_ (pf_map_tail hMpf hMne hp)
              have hlenM : (M.map List.length).sum ≤ n + 1 := by
                refine le_trans ?_ hlen
                exact List.Sublist.sum_le_sum
                  (List.Sublist.map _ (hM ▸ (List.filter_sublist (l := L) (p := p))))
                  (by intro x _; exact Nat.zero_le x)
              have hcount := sum_tail_len M hMne
              have hlen1 : 1 ≤ M.length := by
                cases M with
                | nil => exact absurd rfl hnil
                | cons _ _ => simp
              omega
          nlinarith [hsub]
        have hperm := List.filter_append_perm (fun x => x.headI) L
        have hsplit : kraftSum L
            = kraftSum (L.filter (fun x => x.headI))
              + kraftSum (L.filter (fun x => !x.headI)) := by
          rw [← kraftSum_append]
          exact (kraftSum_perm hperm).symm
        have h1 : kraftSum (L.filter (fun x => x.headI)) ≤ (2 : ℝ)⁻¹ := by
          refine key _ ?_
          intro x hx y hy
          have hx' := List.of_mem_filter hx
          have hy' := List.of_mem_filter hy
          simp only at hx' hy'
          rw [hx', hy']
        have h2 : kraftSum (L.filter (fun x => !x.headI)) ≤ (2 : ℝ)⁻¹ := by
          refine key _ ?_
          intro x hx y hy
          have hx' := List.of_mem_filter hx
          have hy' := List.of_mem_filter hy
          simp only [Bool.not_eq_true'] at hx' hy'
          rw [hx', hy']
        rw [hsplit]
        linarith

/-- **Kraft's inequality**: the Kraft sum of a prefix free list of binary words is at
most one. -/
