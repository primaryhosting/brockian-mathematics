import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma huffman_le_of_kraft : ∀ (n : ℕ) (s : Multiset (ℝ × ℕ)), s.card ≤ n →
    (∀ p ∈ s, 0 ≤ p.1) → mkraft s ≤ 1 → Hmul (s.map Prod.fst) ≤ mcost s := by
  intro n
  induction n with
  | zero =>
      intro s hcard hnn _
      have hs : s = 0 := Multiset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hs
      rw [Hmul_of_card_le_one (by simp)]
      simp
  | succ n ihn =>
      have inner : ∀ (T : ℕ) (s : Multiset (ℝ × ℕ)), (s.map Prod.snd).sum ≤ T →
          s.card ≤ n + 1 → (∀ p ∈ s, 0 ≤ p.1) → mkraft s ≤ 1 →
          Hmul (s.map Prod.fst) ≤ mcost s := by
        intro T
        induction T with
        | zero =>
            intro s hlen hcard hnn hk
            by_cases hsmall : s.card ≤ 1
            · rw [Hmul_of_card_le_one (by simpa using hsmall)]
              exact mcost_nonneg hnn
            · exfalso
              have hcard2 : 2 ≤ s.card := by omega
              have hpos := lengths_pos s hk hcard2
              have hsne : s ≠ 0 := by
                intro h; rw [h] at hcard2; simp at hcard2
              obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hsne
              have h1 : p.2 ≤ (s.map Prod.snd).sum :=
                Multiset.single_le_sum (by intro x _; exact Nat.zero_le x) _
                  (Multiset.mem_map_of_mem _ hp)
              have h2 := hpos p hp
              omega
        | succ T ihT =>
            intro s hlen hcard hnn hk
            by_cases hsmall : s.card ≤ 1
            · rw [Hmul_of_card_le_one (by simpa using hsmall)]
              exact mcost_nonneg hnn
            have hcard2 : 2 ≤ s.card := by omega
            have hpos := lengths_pos s hk hcard2
            have hsne : s ≠ 0 := by
              intro h; rw [h] at hcard2; simp at hcard2
            have hmapne : s.map Prod.snd ≠ 0 := by
              simpa using hsne
            obtain ⟨M, hMmem, hMmax⟩ := exists_max_mem (s.map Prod.snd) hmapne
            obtain ⟨p, hp, hpM⟩ := Multiset.mem_map.mp hMmem
            have hM1 : 1 ≤ M := hpM ▸ hpos p hp
            obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
            have hp' : p = (p.1, k + 1) := by
              rw [← hpM]
            have hsr : s = (p.1, k + 1) ::ₘ s.erase p := by
              conv_lhs => rw [← Multiset.cons_erase hp]
              rw [← hp']
            set r := s.erase p with hr
            have hrsub : ∀ q ∈ r, q ∈ s := by
              intro q hq
              rw [hr] at hq
              exact Multiset.mem_of_mem_erase hq
            by_cases hB : ∃ q ∈ r, q.2 = k + 1
            · -- the maximal length is attained at least twice: merge two smallest weights
              obtain ⟨q0, hq0r, hq0M⟩ := hB
              have hcount : 2 ≤ Multiset.count (k + 1) (s.map Prod.snd) := by
                conv_lhs => rw [show (2:ℕ) = 1 + 1 from rfl]
                rw [hsr]
                simp only [Multiset.map_cons, Multiset.count_cons_self]
                have hmem : (k + 1) ∈ r.map Prod.snd :=
                  Multiset.mem_map.mpr ⟨q0, hq0r, hq0M⟩
                have := Multiset.one_le_count_iff_mem.mpr hmem
                omega
              have hnn' : ∀ x ∈ s.map Prod.fst, 0 ≤ x := by
                intro x hx
                obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
                exact hnn q hq
              have hWne : s.map Prod.fst ≠ 0 := by simpa using hsne
              obtain ⟨a, haW, hamin⟩ := exists_min_mem (s.map Prod.fst) hWne
              obtain ⟨s', hmem', hfst', hsnd', hcost'⟩ :=
                move_min_to_max s a (k + 1) haW hamin hMmem hMmax
              set r' := s'.erase (a, k + 1) with hr'
              have hs'eq : s' = (a, k + 1) ::ₘ r' := (Multiset.cons_erase hmem').symm
              have hr'ne : r'.map Prod.fst ≠ 0 := by
                intro h0
                have hcards : (Multiset.map Prod.fst s).card
                    = (Multiset.map Prod.fst r').card + 1 := by
                  rw [← hfst', hs'eq, Multiset.map_cons, Multiset.card_cons]
                rw [h0, Multiset.card_map] at hcards
                simp at hcards
                omega
              obtain ⟨b, hbW, hbmin⟩ := exists_min_mem (r'.map Prod.fst) hr'ne
              have hMr' : (k + 1) ∈ r'.map Prod.snd := by
                have hc : 2 ≤ Multiset.count (k + 1) (s'.map Prod.snd) := by
                  rw [hsnd']; exact hcount
                rw [hs'eq] at hc
                simp only [Multiset.map_cons, Multiset.count_cons_self] at hc
                exact Multiset.one_le_count_iff_mem.mp (by omega)
              have hMmax' : ∀ y ∈ r'.map Prod.snd, y ≤ k + 1 := by
                intro y hy
                refine hMmax y ?_
                rw [← hsnd', hs'eq]
                simp only [Multiset.map_cons]
                exact Multiset.mem_cons_of_mem hy
              obtain ⟨r'', hmem'', hfst'', hsnd'', hcost''⟩ :=
                move_min_to_max r' b (k + 1) hbW hbmin hMr' hMmax'
              set R := r''.erase (b, k + 1) with hR
              have hr''eq : r'' = (b, k + 1) ::ₘ R := (Multiset.cons_erase hmem'').symm
              have hW : s.map Prod.fst = a ::ₘ b ::ₘ R.map Prod.fst := by
                rw [← hfst', hs'eq, Multiset.map_cons, ← hfst'', hr''eq, Multiset.map_cons]
              have hS : s.map Prod.snd = (k + 1) ::ₘ (k + 1) ::ₘ R.map Prod.snd := by
                rw [← hsnd', hs'eq, Multiset.map_cons, ← hsnd'', hr''eq, Multiset.map_cons]
              -- the merged multiset
              set s2 : Multiset (ℝ × ℕ) := (a + b, k) ::ₘ R with hs2
              have hbmem : b ∈ s.map Prod.fst := by
                rw [hW]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
              have hab : a ≤ b := hamin b hbmem
              have hRb : ∀ x ∈ R.map Prod.fst, b ≤ x := by
                intro x hx
                refine hbmin x ?_
                rw [← hfst'', hr''eq, Multiset.map_cons]
                exact Multiset.mem_cons_of_mem hx
              have hRnn : ∀ x ∈ R.map Prod.fst, 0 ≤ x := by
                intro x hx
                refine hnn' x ?_
                rw [hW]
                exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hx)
              have ha0 : 0 ≤ a := hnn' a haW
              have hb0 : 0 ≤ b := hnn' b hbmem
              -- Kraft
              have hkR : mkraft s = (2:ℝ)⁻¹ ^ (k+1) + ((2:ℝ)⁻¹ ^ (k+1) + mkraft R) := by
                rw [mkraft_def, hS]
                simp [mkraft_def]
              have hk2 : mkraft s2 ≤ 1 := by
                have h2 : mkraft s2 = (2:ℝ)⁻¹ ^ k + mkraft R := by
                  rw [hs2, mkraft_def]
                  simp [mkraft_def]
                have hhalf : (2:ℝ)⁻¹ ^ k = (2:ℝ)⁻¹ ^ (k+1) + (2:ℝ)⁻¹ ^ (k+1) := by
                  rw [pow_succ]
                  ring
                rw [h2, hhalf]
                linarith [hk, hkR]
              -- costs
              have hmcostR : mcost s ≥ a * ((k:ℝ)+1) + (b * ((k:ℝ)+1) + mcost R) := by
                have e1 : mcost s' = a * (((k+1 : ℕ)):ℝ) + mcost r' := by
                  rw [hs'eq, mcost_cons]
                have e2 : mcost r'' = b * (((k+1 : ℕ)):ℝ) + mcost R := by
                  rw [hr''eq, mcost_cons]
                have : ((k+1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
                rw [this] at e1 e2
                linarith [hcost', hcost'']
              have hcost2 : mcost s2 = (a + b) * (k:ℝ) + mcost R := by
                rw [hs2, mcost_cons]
              have hcards2 : s2.card ≤ n := by
                have h1 : s.card = R.card + 2 := by
                  have := congrArg Multiset.card hW
                  simpa [Multiset.card_map] using this
                have h2 : s2.card = R.card + 1 := by
                  rw [hs2]; simp
                omega
              have hnn2 : ∀ q ∈ s2, 0 ≤ q.1 := by
                intro q hq
                rw [hs2] at hq
                rcases Multiset.mem_cons.mp hq with rfl | hq
                · simpa using add_nonneg ha0 hb0
                · exact hRnn q.1 (Multiset.mem_map_of_mem _ hq)
              have hfst2 : s2.map Prod.fst = (a + b) ::ₘ R.map Prod.fst := by
                rw [hs2]; simp
              have hstep : Hmul (s.map Prod.fst) = (a + b) + Hmul (s2.map Prod.fst) := by
                rw [hW, hfst2]
                exact Hmul_step a b (R.map Prod.fst) hab hRb
              have hIH := ihn s2 hcards2 hnn2 hk2
              rw [hstep, hcost2] at *
              linarith [hIH, hmcostR]
            · -- the maximal length is attained only once: shorten that codeword
              push_neg at hB
              have hlt : ∀ q ∈ r, q.2 < k + 1 := by
                intro q hq
                have h1 : q.2 ≤ k + 1 :=
                  hMmax q.2 (Multiset.mem_map_of_mem _ (hrsub q hq))
                have h2 := hB q hq
                omega
              have hslack : mkraft s + (2:ℝ)⁻¹ ^ (k+1) ≤ 1 := by
                rw [hsr]
                rw [hsr] at hk
                exact kraft_slack_of_unique_max (k+1) p.1 r (by omega) hlt hk
              set s1 : Multiset (ℝ × ℕ) := (p.1, k) ::ₘ r with hs1
              have hkr : mkraft s = (2:ℝ)⁻¹ ^ (k+1) + mkraft r := by
                conv_lhs => rw [hsr]
                rw [mkraft_cons]
              have hk1 : mkraft s1 ≤ 1 := by
                rw [hs1, mkraft_cons]
                have hhalf : (2:ℝ)⁻¹ ^ k = (2:ℝ)⁻¹ ^ (k+1) + (2:ℝ)⁻¹ ^ (k+1) := by
                  rw [pow_succ]; ring
                rw [hhalf]
                linarith [hslack, hkr]
              have hp1 : 0 ≤ p.1 := hnn p hp
              have hcost1 : mcost s1 ≤ mcost s := by
                conv_rhs => rw [hsr]
                rw [hs1, mcost_cons, mcost_cons]
                have hcast : ((k+1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
                rw [hcast]
                nlinarith [hp1]
              have hfst : s1.map Prod.fst = s.map Prod.fst := by
                conv_rhs => rw [hsr]
                rw [hs1]
                simp
              have hlen1 : (s1.map Prod.snd).sum ≤ T := by
                have h1 : (s.map Prod.snd).sum = (k+1) + (r.map Prod.snd).sum := by
                  conv_lhs => rw [hsr]
                  simp
                have h2 : (s1.map Prod.snd).sum = k + (r.map Prod.snd).sum := by
                  rw [hs1]; simp
                omega
              have hcard1 : s1.card ≤ n + 1 := by
                have h1 : s.card = r.card + 1 := by
                  conv_lhs => rw [hsr]
                  simp
                have h2 : s1.card = r.card + 1 := by rw [hs1]; simp
                omega
              have hnn1 : ∀ q ∈ s1, 0 ≤ q.1 := by
                intro q hq
                rw [hs1] at hq
                rcases Multiset.mem_cons.mp hq with rfl | hq
                · simpa using hp1
                · exact hnn q (hrsub q hq)
              calc Hmul (s.map Prod.fst) = Hmul (s1.map Prod.fst) := by rw [hfst]
                _ ≤ mcost s1 := ihT s1 hlen1 hcard1 hnn1 hk1
                _ ≤ mcost s := hcost1
      intro s hcard hnn hk
      exact inner ((s.map Prod.snd).sum) s le_rfl hcard hnn hk


end CS

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- A list of binary words is *prefix free* if no word is a prefix of another one. -/
