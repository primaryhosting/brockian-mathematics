import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/
noncomputable def Hmul (m : Multiset ℝ) : ℝ := hcost (m.sort (· ≤ ·))

/-- The expected codeword length of a multiset of (weight, codeword length) pairs. -/
noncomputable def mcost (s : Multiset (ℝ × ℕ)) : ℝ := (s.map (fun p => p.1 * (p.2 : ℝ))).sum

/-- The Kraft sum of a multiset of (weight, codeword length) pairs. -/
noncomputable def mkraft (s : Multiset (ℝ × ℕ)) : ℝ :=
  ((s.map Prod.snd).map (fun l => (2 : ℝ)⁻¹ ^ l)).sum

@[simp] lemma mcost_zero : mcost 0 = 0 := by simp [mcost]

@[simp] lemma mcost_cons (p : ℝ × ℕ) (s : Multiset (ℝ × ℕ)) :
    mcost (p ::ₘ s) = p.1 * (p.2 : ℝ) + mcost s := by simp [mcost]

@[simp] lemma mkraft_zero : mkraft 0 = 0 := by simp [mkraft]

@[simp] lemma mkraft_cons (p : ℝ × ℕ) (s : Multiset (ℝ × ℕ)) :
    mkraft (p ::ₘ s) = (2 : ℝ)⁻¹ ^ p.2 + mkraft s := by simp [mkraft]

lemma mkraft_congr {s t : Multiset (ℝ × ℕ)} (h : s.map Prod.snd = t.map Prod.snd) :
    mkraft s = mkraft t := by simp [mkraft, h]

lemma mkraft_nonneg (s : Multiset (ℝ × ℕ)) : 0 ≤ mkraft s := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx
  positivity

lemma mcost_nonneg {s : Multiset (ℝ × ℕ)} (h : ∀ p ∈ s, 0 ≤ p.1) : 0 ≤ mcost s := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact mul_nonneg (h y hy) (Nat.cast_nonneg _)

/-- The sorted list of a sorted list is itself. -/
lemma sort_coe_of_sorted {l : List ℝ} (hs : l.Pairwise (· ≤ ·)) :
    (↑l : Multiset ℝ).sort (· ≤ ·) = l := by
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
    (Multiset.pairwise_sort _ _) hs ?_
  exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)

lemma Hmul_of_card_le_one {m : Multiset ℝ} (h : m.card ≤ 1) : Hmul m = 0 := by
  unfold Hmul
  have hlen : (m.sort (· ≤ ·)).length ≤ 1 := by
    rw [Multiset.length_sort]; exact h
  match hm : m.sort (· ≤ ·) with
  | [] => simp
  | [a] => simp
  | a :: b :: t => rw [hm] at hlen; simp at hlen

/-- One step of Huffman's algorithm, at the level of multisets of weights. -/
lemma Hmul_step (a b : ℝ) (t : Multiset ℝ) (hab : a ≤ b) (hbt : ∀ x ∈ t, b ≤ x) :
    Hmul (a ::ₘ b ::ₘ t) = (a + b) + Hmul ((a + b) ::ₘ t) := by
  have hts : (t.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have htmem : ∀ x ∈ t.sort (· ≤ ·), b ≤ x := by
    intro x hx
    exact hbt x (by rw [← Multiset.sort_eq t (· ≤ ·)]; exact hx)
  have hsorted : (a :: b :: t.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨htmem, hts⟩⟩
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · exact h ▸ hab
    · exact hab.trans (htmem y h)
  have hs1 : (a ::ₘ b ::ₘ t).sort (· ≤ ·) = a :: b :: t.sort (· ≤ ·) := by
    have : ((a :: b :: t.sort (· ≤ ·) : List ℝ) : Multiset ℝ) = a ::ₘ b ::ₘ t := by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.sort_eq]
    rw [← this, sort_coe_of_sorted hsorted]
  have hins : ((a + b) ::ₘ t).sort (· ≤ ·)
      = List.orderedInsert (· ≤ ·) (a + b) (t.sort (· ≤ ·)) := by
    have hp : ((List.orderedInsert (· ≤ ·) (a + b) (t.sort (· ≤ ·)) : List ℝ) : Multiset ℝ)
        = (a + b) ::ₘ t := by
      have := List.perm_orderedInsert (α := ℝ) (· ≤ ·) (a + b) (t.sort (· ≤ ·))
      have h2 : ((List.orderedInsert (· ≤ ·) (a + b) (t.sort (· ≤ ·)) : List ℝ) : Multiset ℝ)
          = ((a + b) :: t.sort (· ≤ ·) : List ℝ) := Quot.sound this
      rw [h2, ← Multiset.cons_coe, Multiset.sort_eq]
    rw [← hp, sort_coe_of_sorted (List.Pairwise.orderedInsert _ _ hts)]
  rw [Hmul, Hmul, hs1, hins, hcost_cons_cons]


/-- A nonempty multiset in a linear order has a least element. -/
lemma exists_min_mem {α : Type*} [LinearOrder α] :
    ∀ (m : Multiset α), m ≠ 0 → ∃ a ∈ m, ∀ x ∈ m, a ≤ x := by
  intro m
  refine Multiset.induction_on m ?_ ?_
  · intro h; exact absurd rfl h
  · intro a s ih _
    rcases eq_or_ne s 0 with rfl | hs
    · exact ⟨a, by simp, by intro x hx; simp at hx; exact le_of_eq hx.symm⟩
    · obtain ⟨b, hb, hbmin⟩ := ih hs
      rcases le_total a b with hab | hab
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hab.trans (hbmin x hx)
      · refine ⟨b, Multiset.mem_cons_of_mem hb, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hab
        · exact hbmin x hx

/-- A nonempty multiset in a linear order has a greatest element. -/
lemma exists_max_mem {α : Type*} [LinearOrder α] :
    ∀ (m : Multiset α), m ≠ 0 → ∃ a ∈ m, ∀ x ∈ m, x ≤ a := by
  intro m
  refine Multiset.induction_on m ?_ ?_
  · intro h; exact absurd rfl h
  · intro a s ih _
    rcases eq_or_ne s 0 with rfl | hs
    · exact ⟨a, by simp, by intro x hx; simp at hx; exact le_of_eq hx⟩
    · obtain ⟨b, hb, hbmax⟩ := ih hs
      rcases le_total a b with hab | hab
      · refine ⟨b, Multiset.mem_cons_of_mem hb, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hab
        · exact hbmax x hx
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact (hbmax x hx).trans hab

/-- In a prefix code with at least two symbols all codewords are nonempty. -/
lemma lengths_pos (s : Multiset (ℝ × ℕ)) (hk : mkraft s ≤ 1) (hcard : 2 ≤ s.card) :
    ∀ p ∈ s, 1 ≤ p.2 := by
  intro p hp
  by_contra hcon
  have hp2 : p.2 = 0 := by omega
  have hs : s = p ::ₘ s.erase p := (Multiset.cons_erase hp).symm
  have hcard' : 1 ≤ (s.erase p).card := by
    have := Multiset.card_erase_of_mem hp
    rw [Nat.pred_eq_sub_one] at this
    omega
  have hne : s.erase p ≠ 0 := by
    intro h; rw [h] at hcard'; simp at hcard'
  obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hne
  have hs2 : s.erase p = q ::ₘ (s.erase p).erase q := (Multiset.cons_erase hq).symm
  have e1 := mkraft_cons p (s.erase p)
  rw [← hs] at e1
  have e2 := mkraft_cons q ((s.erase p).erase q)
  rw [← hs2] at e2
  rw [e1, e2, hp2] at hk
  have h1 : (0:ℝ) < (2 : ℝ)⁻¹ ^ q.2 := by positivity
  have h2 : (0:ℝ) ≤ mkraft ((s.erase p).erase q) := mkraft_nonneg _
  simp only [pow_zero] at hk
  linarith

/-- Exchange argument: a symbol of minimal weight may be assumed to have a codeword of
maximal length, without increasing the expected length. -/
lemma move_min_to_max (s : Multiset (ℝ × ℕ)) (a : ℝ) (M : ℕ)
    (ha : a ∈ s.map Prod.fst) (hamin : ∀ x ∈ s.map Prod.fst, a ≤ x)
    (hMmem : M ∈ s.map Prod.snd) (hMmax : ∀ y ∈ s.map Prod.snd, y ≤ M) :
    ∃ s' : Multiset (ℝ × ℕ), (a, M) ∈ s' ∧ s'.map Prod.fst = s.map Prod.fst ∧
      s'.map Prod.snd = s.map Prod.snd ∧ mcost s' ≤ mcost s := by
  obtain ⟨pa, hpa, hpa1⟩ := Multiset.mem_map.mp ha
  obtain ⟨pm, hpm, hpm2⟩ := Multiset.mem_map.mp hMmem
  by_cases h : pa.2 = M
  · refine ⟨s, ?_, rfl, rfl, le_rfl⟩
    have : pa = (a, M) := Prod.ext hpa1 h
    exact this ▸ hpa
  · have hne : pm ≠ pa := by
      intro hh
      exact h (by rw [← hh, hpm2])
    have hpm' : pm ∈ s.erase pa := (Multiset.mem_erase_of_ne hne).mpr hpm
    have hs : s = pa ::ₘ pm ::ₘ (s.erase pa).erase pm := by
      rw [Multiset.cons_erase hpm', Multiset.cons_erase hpa]
    set R := (s.erase pa).erase pm with hR
    have hpa2le : (pa.2 : ℝ) ≤ (M : ℝ) := by
      have := hMmax pa.2 (Multiset.mem_map_of_mem _ hpa)
      exact_mod_cast this
    have hple : a ≤ pm.1 := hamin pm.1 (Multiset.mem_map_of_mem _ hpm)
    refine ⟨(a, M) ::ₘ (pm.1, pa.2) ::ₘ R, Multiset.mem_cons_self _ _, ?_, ?_, ?_⟩
    · conv_rhs => rw [hs]
      simp [hpa1]
    · conv_rhs => rw [hs]
      simp [hpm2, Multiset.cons_swap]
    · conv_rhs => rw [hs]
      simp only [mcost_cons]
      rw [hpa1, hpm2]
      nlinarith [hpa2le, hple]

/-- If a unique codeword has maximal length `M`, then the Kraft sum has slack at least
`2 ^ (-M)`. -/
lemma kraft_slack_of_unique_max (M : ℕ) (a : ℝ) (r : Multiset (ℝ × ℕ))
    (hM : 1 ≤ M) (hlt : ∀ q ∈ r, q.2 < M) (hk : mkraft ((a, M) ::ₘ r) ≤ 1) :
    mkraft ((a, M) ::ₘ r) + (2 : ℝ)⁻¹ ^ M ≤ 1 := by
  have hle : ∀ q ∈ (a, M) ::ₘ r, q.2 ≤ M := by
    intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact le_rfl
    · exact (hlt q hq).le
  have hscale : mkraft ((a, M) ::ₘ r) * 2 ^ M
      = (((((a, M) ::ₘ r).map (fun q => 2 ^ (M - q.2))).sum : ℕ) : ℝ) := by
    have h1 : mkraft ((a, M) ::ₘ r)
        = (((a, M) ::ₘ r).map (fun q => (2 : ℝ)⁻¹ ^ q.2)).sum := by
      simp [mkraft, Multiset.map_map, Function.comp]
    have h2 : (((((a, M) ::ₘ r).map (fun q => 2 ^ (M - q.2))).sum : ℕ) : ℝ)
        = (((a, M) ::ₘ r).map (fun q => ((2:ℝ)) ^ (M - q.2))).sum := by
      push_cast
      rw [Multiset.map_map]
      refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
      intro q _
      simp
    rw [h1, ← Multiset.sum_map_mul_right, h2]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro q hq
    have hq2 : q.2 ≤ M := hle q hq
    have hpow : (2 : ℝ) ^ M = 2 ^ (M - q.2) * 2 ^ q.2 := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, inv_pow, ← mul_assoc, inv_mul_eq_div]
    field_simp
  set N : ℕ := ((((a, M) ::ₘ r).map (fun q => 2 ^ (M - q.2))).sum : ℕ) with hN
  have hodd : N % 2 = 1 := by
    have hsum : N = 1 + (r.map (fun q => 2 ^ (M - q.2))).sum := by
      rw [hN]
      simp
    have heven : 2 ∣ (r.map (fun q => 2 ^ (M - q.2))).sum := by
      refine Multiset.dvd_sum ?_
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
      have hq1 : 1 ≤ M - q.2 := by have := hlt q hq; omega
      exact dvd_pow_self 2 (by omega)
    obtain ⟨c, hc⟩ := heven
    omega
  have hpow : (0:ℝ) < 2 ^ M := by positivity
  have hNle : (N : ℝ) ≤ 2 ^ M := by
    rw [← hscale]
    nlinarith [hk, hpow]
  have hNleN : N ≤ 2 ^ M := by exact_mod_cast hNle
  have hpowEven : 2 ∣ 2 ^ M := dvd_pow_self 2 (by omega)
  have hNne : N ≠ 2 ^ M := by
    intro hEq
    obtain ⟨c, hc⟩ := hpowEven
    omega
  have hNlt : N + 1 ≤ 2 ^ M := by omega
  have hNlt' : (N : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast hNlt
  have hmain : mkraft ((a, M) ::ₘ r) * 2 ^ M + 1 ≤ 2 ^ M := by rw [hscale]; exact hNlt'
  rw [inv_pow, ← sub_nonneg]
  have hrw : 1 - (mkraft ((a, M) ::ₘ r) + ((2:ℝ) ^ M)⁻¹)
      = (2 ^ M - mkraft ((a, M) ::ₘ r) * 2 ^ M - 1) / 2 ^ M := by
    field_simp
    ring
  rw [hrw]
  exact div_nonneg (by linarith) hpow.le


lemma mkraft_def (s : Multiset (ℝ × ℕ)) :
    mkraft s = ((s.map Prod.snd).map (fun l => (2 : ℝ)⁻¹ ^ l)).sum := rfl

/-- **Huffman's algorithm is optimal**, in terms of codeword lengths: the value it computes
is a lower bound for the expected length of any assignment of codeword lengths satisfying
Kraft's inequality. -/
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
def PFList (L : List (List Bool)) : Prop :=
  L.Pairwise (fun x y => ¬ (x <+: y) ∧ ¬ (y <+: x))

/-- The Kraft sum `∑ 2 ^ (-|x|)` of a list of binary words. -/
noncomputable def kraftSum (L : List (List Bool)) : ℝ :=
  (L.map (fun x => (2 : ℝ)⁻¹ ^ x.length)).sum

@[simp] lemma kraftSum_nil : kraftSum [] = 0 := by simp [kraftSum]

lemma kraftSum_cons (x : List Bool) (L : List (List Bool)) :
    kraftSum (x :: L) = (2 : ℝ)⁻¹ ^ x.length + kraftSum L := by simp [kraftSum]

lemma kraftSum_append (L₁ L₂ : List (List Bool)) :
    kraftSum (L₁ ++ L₂) = kraftSum L₁ + kraftSum L₂ := by
  simp [kraftSum]

lemma kraftSum_perm {L₁ L₂ : List (List Bool)} (h : L₁.Perm L₂) :
    kraftSum L₁ = kraftSum L₂ := (h.map _).sum_eq

/-- A prefix free list containing the empty word is the singleton `[[]]`. -/
lemma PFList.eq_singleton_nil {L : List (List Bool)} (h : PFList L) (hm : [] ∈ L) :
    L = [[]] := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
  have hp := List.pairwise_append.mp h
  obtain ⟨-, hp2, hcross⟩ := hp
  have hs : s = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro a ha
    exact (hcross a ha [] (by simp)).2 (List.nil_prefix)
  have ht : t = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro a ha
    exact (List.pairwise_cons.mp hp2).1 a ha |>.1 (List.nil_prefix)
  subst hs; subst ht; rfl

private lemma kraft_half (L : List (List Bool)) (h : ∀ x ∈ L, x ≠ []) :
    kraftSum L = (2 : ℝ)⁻¹ * kraftSum (L.map List.tail) := by
  unfold kraftSum
  rw [List.map_map]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro a ha
  have : a.length = (a.tail).length + 1 := by
    cases a with
    | nil => exact absurd rfl (h [] ha)
    | cons b bs => simp
  rw [this]
  simp [pow_succ]
  ring

private lemma pf_map_tail {L : List (List Bool)} (h : PFList L)
    (hne : ∀ x ∈ L, x ≠ []) (hhead : ∀ x ∈ L, ∀ y ∈ L, x.headI = y.headI) :
    PFList (L.map List.tail) := by
  rw [PFList, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro a b ha hb hab
  have hane := hne a ha
  have hbne := hne b hb
  have hh := hhead a ha b hb
  constructor
  · intro hpre
    refine hab.1 ?_
    obtain ⟨a1, a2, rfl⟩ : ∃ c cs, a = c :: cs := by
      cases a with
      | nil => exact absurd rfl hane
      | cons c cs => exact ⟨c, cs, rfl⟩
    obtain ⟨b1, b2, rfl⟩ : ∃ c cs, b = c :: cs := by
      cases b with
      | nil => exact absurd rfl hbne
      | cons c cs => exact ⟨c, cs, rfl⟩
    simp only [List.headI] at hh
    simp only [List.tail] at hpre
    exact List.cons_prefix_cons.mpr ⟨hh, hpre⟩
  · intro hpre
    refine hab.2 ?_
    obtain ⟨a1, a2, rfl⟩ : ∃ c cs, a = c :: cs := by
      cases a with
      | nil => exact absurd rfl hane
      | cons c cs => exact ⟨c, cs, rfl⟩
    obtain ⟨b1, b2, rfl⟩ : ∃ c cs, b = c :: cs := by
      cases b with
      | nil => exact absurd rfl hbne
      | cons c cs => exact ⟨c, cs, rfl⟩
    simp only [List.headI] at hh
    simp only [List.tail] at hpre
    exact List.cons_prefix_cons.mpr ⟨hh.symm, hpre⟩

private lemma sum_tail_len : ∀ (M : List (List Bool)), (∀ x ∈ M, x ≠ []) →
    ((M.map List.tail).map List.length).sum + M.length = (M.map List.length).sum := by
  intro M
  induction M with
  | nil => simp
  | cons y ys ih =>
      intro h
      have hy : y ≠ [] := h y (by simp)
      have hrest : ∀ x ∈ ys, x ≠ [] := fun x hx => h x (by simp [hx])
      have := ih hrest
      cases y with
      | nil => exact absurd rfl hy
      | cons c cs => simp at this ⊢; omega

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
theorem kraft_inequality (L : List (List Bool)) (h : PFList L) : kraftSum L ≤ 1 :=
  kraft_aux (L.map List.length).sum L le_rfl h

end CS

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {ι : Type*}

/-- A binary code tree whose leaves are labelled by symbols of type `ι`. -/
inductive HTree (ι : Type*) where
  | leaf (i : ι) : HTree ι
  | node (l r : HTree ι) : HTree ι
  deriving Inhabited

namespace HTree

/-- The list of leaf labels of a tree, left to right. -/
def elems : HTree ι → List ι
  | leaf i => [i]
  | node l r => elems l ++ elems r

@[simp] lemma elems_leaf (i : ι) : (leaf i).elems = [i] := rfl
@[simp] lemma elems_node (l r : HTree ι) : (node l r).elems = l.elems ++ r.elems := rfl

lemma elems_ne_nil (T : HTree ι) : T.elems ≠ [] := by
  induction T with
  | leaf i => simp
  | node l r ihl _ => simp [ihl]

/-- Total weight of the leaves of a tree. -/
def wsum (w : ι → ℝ) (T : HTree ι) : ℝ := (T.elems.map w).sum

@[simp] lemma wsum_leaf (w : ι → ℝ) (i : ι) : wsum w (leaf i) = w i := by simp [wsum]

@[simp] lemma wsum_node (w : ι → ℝ) (l r : HTree ι) :
    wsum w (node l r) = wsum w l + wsum w r := by simp [wsum]

/-- The cost (weighted external path length) of a tree. -/
def tcost (w : ι → ℝ) : HTree ι → ℝ
  | leaf _ => 0
  | node l r => tcost w l + tcost w r + wsum w l + wsum w r

@[simp] lemma tcost_leaf (w : ι → ℝ) (i : ι) : tcost w (leaf i) = 0 := rfl

@[simp] lemma tcost_node (w : ι → ℝ) (l r : HTree ι) :
    tcost w (node l r) = tcost w l + tcost w r + wsum w l + wsum w r := rfl

/-- The codeword assigned to a symbol by a tree: the path from the root to its leaf. -/
def codeOf [DecidableEq ι] : HTree ι → ι → List Bool
  | leaf _, _ => []
  | node l r, i => if i ∈ l.elems then false :: codeOf l i else true :: codeOf r i

@[simp] lemma codeOf_leaf [DecidableEq ι] (j i : ι) : codeOf (leaf j) i = [] := rfl

lemma codeOf_node [DecidableEq ι] (l r : HTree ι) (i : ι) :
    codeOf (node l r) i = if i ∈ l.elems then false :: codeOf l i else true :: codeOf r i := rfl

/-- The code produced by a tree with distinct leaf labels is prefix free. -/
lemma codeOf_prefixFree [DecidableEq ι] :
    ∀ (T : HTree ι), T.elems.Nodup → ∀ i ∈ T.elems, ∀ j ∈ T.elems, i ≠ j →
      ¬ (codeOf T i <+: codeOf T j) := by
  intro T
  induction T with
  | leaf k =>
      intro _ i hi j hj hij
      simp only [elems_leaf, List.mem_singleton] at hi hj
      exact absurd (hi.trans hj.symm) hij
  | node l r ihl ihr =>
      intro hnd i hi j hj hij
      simp only [elems_node, List.nodup_append] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      simp only [elems_node, List.mem_append] at hi hj
      by_cases hil : i ∈ l.elems <;> by_cases hjl : j ∈ l.elems
      · rw [codeOf_node, codeOf_node, if_pos hil, if_pos hjl]
        simpa using ihl hl i hil j hjl hij
      · have hjr : j ∈ r.elems := hj.resolve_left hjl
        rw [codeOf_node, codeOf_node, if_pos hil, if_neg hjl]
        simp
      · have hir : i ∈ r.elems := hi.resolve_left hil
        rw [codeOf_node, codeOf_node, if_neg hil, if_pos hjl]
        simp
      · have hir : i ∈ r.elems := hi.resolve_left hil
        have hjr : j ∈ r.elems := hj.resolve_left hjl
        rw [codeOf_node, codeOf_node, if_neg hil, if_neg hjl]
        simpa using ihr hr i hir j hjr hij

/-- The cost of a tree equals the weighted sum of the codeword lengths it assigns. -/
lemma tcost_eq_sum_codeOf [DecidableEq ι] (w : ι → ℝ) :
    ∀ (T : HTree ι), T.elems.Nodup →
      tcost w T = (T.elems.map (fun i => w i * ((codeOf T i).length : ℝ))).sum := by
  intro T
  induction T with
  | leaf k => intro _; simp
  | node l r ihl ihr =>
      intro hnd
      simp only [elems_node, List.nodup_append] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      have hL : l.elems.map (fun i => w i * ((codeOf (node l r) i).length : ℝ))
          = l.elems.map (fun i => w i * ((codeOf l i).length : ℝ) + w i) := by
        refine List.map_congr_left ?_
        intro a ha
        rw [codeOf_node, if_pos ha]
        push_cast [List.length_cons]
        ring
      have hR : r.elems.map (fun i => w i * ((codeOf (node l r) i).length : ℝ))
          = r.elems.map (fun i => w i * ((codeOf r i).length : ℝ) + w i) := by
        refine List.map_congr_left ?_
        intro a ha
        have hna : a ∉ l.elems := fun h => hdisj a h a ha rfl
        rw [codeOf_node, if_neg hna]
        push_cast [List.length_cons]
        ring
      rw [tcost_node, elems_node, List.map_append, List.sum_append, hL, hR,
        List.sum_map_add, List.sum_map_add, ihl hl, ihr hr]
      simp only [wsum]
      ring

end HTree

end CS

import RequestProject.Tree

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {ι : Type*}

/-- Huffman's algorithm run on a list of weights: repeatedly merge the two smallest
weights, accumulating the merged weights.  For a sorted input this is exactly the total
cost of the Huffman code. -/
noncomputable def hcost : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (a + b) + hcost (List.orderedInsert (· ≤ ·) (a + b) rest)
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    have h := (List.perm_orderedInsert (· ≤ ·) (a + b) rest).length_eq
    simp only [List.length_cons] at h
    omega

@[simp] lemma hcost_nil : hcost [] = 0 := by rw [hcost]
@[simp] lemma hcost_singleton (a : ℝ) : hcost [a] = 0 := by rw [hcost]

lemma hcost_cons_cons (a b : ℝ) (rest : List ℝ) :
    hcost (a :: b :: rest) = (a + b) + hcost (List.orderedInsert (· ≤ ·) (a + b) rest) := by
  rw [hcost]

/-- Huffman's algorithm on a forest of weighted trees. -/
noncomputable def hforest : List (ℝ × HTree ι) → Option (HTree ι)
  | [] => none
  | [(_, t)] => some t
  | (a, s) :: (b, t) :: rest =>
      hforest (List.orderedInsert (fun p q => p.1 ≤ q.1) (a + b, HTree.node s t) rest)
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    have h := (List.perm_orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1)
      (a + b, HTree.node s t) rest).length_eq
    simp only [List.length_cons] at h
    omega

lemma map_fst_orderedInsert (x : ℝ × HTree ι) :
    ∀ (l : List (ℝ × HTree ι)),
      (List.orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1) x l).map Prod.fst
        = List.orderedInsert (· ≤ ·) x.1 (l.map Prod.fst) := by
  intro l
  induction l with
  | nil => simp [List.orderedInsert]
  | cons y ys ih =>
      by_cases h : x.1 ≤ y.1
      · simp [List.orderedInsert, h]
      · simp [List.orderedInsert, h, ih]

/-- Structure theorem for Huffman's algorithm on a forest: the resulting tree has the
leaves of the whole forest, and its cost is the sum of the costs of the trees of the
forest plus the value computed by Huffman's algorithm on the weights. -/
lemma hforest_spec (w : ι → ℝ) :
    ∀ (F : List (ℝ × HTree ι)) (T : HTree ι), hforest F = some T →
      (∀ p ∈ F, p.1 = HTree.wsum w p.2) →
      (T.elems.Perm (F.flatMap (fun p => p.2.elems))) ∧
        HTree.tcost w T
          = (F.map (fun p => HTree.tcost w p.2)).sum + hcost (F.map Prod.fst) := by
  intro F
  induction F using hforest.induct with
  | case1 =>
      intro T hT _
      rw [hforest] at hT
      exact absurd hT (by simp)
  | case2 a t =>
      intro T hT _
      rw [hforest] at hT
      have : T = t := by simpa using hT.symm
      subst this
      constructor
      · simp
      · simp
  | case3 a s b t rest ih =>
      intro T hT hw
      rw [hforest] at hT
      set x : ℝ × HTree ι := (a + b, HTree.node s t) with hx
      set F' : List (ℝ × HTree ι) :=
        List.orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1) x rest with hF'
      have hperm : F'.Perm (x :: rest) :=
        List.perm_orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1) x rest
      have has : a = HTree.wsum w s := hw (a, s) (by simp)
      have hbt : b = HTree.wsum w t := hw (b, t) (by simp)
      have hw' : ∀ p ∈ F', p.1 = HTree.wsum w p.2 := by
        intro p hp
        have : p ∈ x :: rest := hperm.mem_iff.mp hp
        rcases List.mem_cons.mp this with h | h
        · subst h; simp [hx, has, hbt]
        · exact hw p (by simp [h])
      obtain ⟨hE, hC⟩ := ih T hT hw'
      have hflat : (F'.flatMap (fun p => p.2.elems)).Perm
          (((a, s) :: (b, t) :: rest).flatMap (fun p => p.2.elems)) := by
        refine (hperm.flatMap_right _).trans ?_
        simp [hx, List.flatMap_cons, List.append_assoc]
      refine ⟨hE.trans hflat, ?_⟩
      have hsum : (F'.map (fun p => HTree.tcost w p.2)).sum
          = HTree.tcost w (HTree.node s t) + (rest.map (fun p => HTree.tcost w p.2)).sum := by
        have := (hperm.map (fun p => HTree.tcost w p.2)).sum_eq
        simpa [hx] using this
      have hmapfst : F'.map Prod.fst = List.orderedInsert (· ≤ ·) (a + b) (rest.map Prod.fst) := by
        simpa [hx] using map_fst_orderedInsert x rest
      rw [hC, hsum, hmapfst]
      simp only [List.map_cons, List.sum_cons, hcost_cons_cons, HTree.tcost_node]
      rw [← has, ← hbt]
      ring

end CS

import RequestProject.Huffman

namespace CS
/-!
# Sanity checks

Small worked examples confirming that the definitions compute the intended quantities:
for the weights `1, 2, 3` Huffman coding gives codeword lengths `2, 2, 1`, i.e. an
expected length of `1*2 + 2*2 + 3*1 = 9`.
-/
example : hcost [1, 2, 3] = 9 := by
  rw [hcost_cons_cons]
  norm_num [List.orderedInsert, hcost_cons_cons]

example : Hmul ({1, 2, 3} : Multiset ℝ) = 9 := by
  have : ({1, 2, 3} : Multiset ℝ).sort (· ≤ ·) = [1, 2, 3] := by
    refine sort_coe_of_sorted (by norm_num)
  rw [Hmul, this, hcost_cons_cons]
  norm_num [List.orderedInsert, hcost_cons_cons]

example (w : Fin 3 → ℝ) (h0 : w 0 = 1) (h1 : w 1 = 2) (h2 : w 2 = 3) :
    expLength w (huffmanCode w) = 9 := by
  rw [huffmanCode_expLength]
  have hm : (Finset.univ.val.map w : Multiset ℝ) = {w 0, w 1, w 2} := rfl
  rw [hm, h0, h1, h2]
  have : ({1, 2, 3} : Multiset ℝ).sort (· ≤ ·) = [1, 2, 3] := by
    refine sort_coe_of_sorted (by norm_num)
  rw [Hmul, this, hcost_cons_cons]
  norm_num [List.orderedInsert, hcost_cons_cons]

end CS

import RequestProject.Lower
import RequestProject.Kraft

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance instIsTransWle : IsTrans (ℝ × HTree ι) (fun p q => p.1 ≤ q.1) :=
  ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩

instance instTotalWle : Std.Total (fun p q : ℝ × HTree ι => p.1 ≤ q.1) :=
  ⟨fun a b => le_total a.1 b.1⟩

/-- A code is a *prefix code* if no codeword is a prefix of the codeword of another
symbol. -/
def IsPrefixCode (c : ι → List Bool) : Prop := ∀ i j, i ≠ j → ¬ (c i <+: c j)

/-- The expected codeword length of the code `c` for the weights `w`. -/
noncomputable def expLength (w : ι → ℝ) (c : ι → List Bool) : ℝ :=
  ∑ i, w i * ((c i).length : ℝ)

/-- The initial forest of Huffman's algorithm: one leaf per symbol, sorted by weight. -/
noncomputable def initialForest (w : ι → ℝ) : List (ℝ × HTree ι) :=
  List.insertionSort (fun p q => p.1 ≤ q.1)
    (Finset.univ.toList.map (fun i => (w i, HTree.leaf i)))

/-- The code produced by Huffman's algorithm. -/
noncomputable def huffmanCode (w : ι → ℝ) : ι → List Bool :=
  (hforest (initialForest w)).elim (fun _ => []) (fun T => HTree.codeOf T)

omit [Fintype ι] [DecidableEq ι] in
lemma hforest_isSome : ∀ (F : List (ℝ × HTree ι)), F ≠ [] → ∃ T, hforest F = some T := by
  intro F
  induction F using hforest.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 a t => intro _; exact ⟨t, by rw [hforest]⟩
  | case3 a s b t rest ih =>
      intro _
      have hne : List.orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1)
          (a + b, HTree.node s t) rest ≠ [] := by
        intro h
        have := (List.perm_orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1)
          (a + b, HTree.node s t) rest).length_eq
        rw [h] at this
        simp at this
      obtain ⟨T, hT⟩ := ih hne
      exact ⟨T, by rw [hforest]; exact hT⟩

omit [DecidableEq ι] in
lemma initialForest_perm (w : ι → ℝ) :
    (initialForest w).Perm (Finset.univ.toList.map (fun i => (w i, HTree.leaf i))) :=
  List.perm_insertionSort _ _

omit [DecidableEq ι] in
lemma initialForest_sorted (w : ι → ℝ) :
    ((initialForest w).map Prod.fst).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact List.pairwise_insertionSort _ _

omit [DecidableEq ι] in
/-- The tree built by Huffman's algorithm: it has all symbols as leaves, and its cost is
the value computed by Huffman's algorithm on the multiset of weights. -/
lemma exists_huffman_tree (w : ι → ℝ) (hne : Finset.univ.toList (α := ι) ≠ []) :
    ∃ T : HTree ι, hforest (initialForest w) = some T ∧
      T.elems.Perm (Finset.univ.toList) ∧
      HTree.tcost w T = Hmul (Finset.univ.val.map w) := by
  have hF0ne : initialForest w ≠ [] := by
    intro h
    have hlen := (initialForest_perm w).length_eq
    rw [h] at hlen
    simp only [List.length_nil, List.length_map] at hlen
    exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
  obtain ⟨T, hT⟩ := hforest_isSome (initialForest w) hF0ne
  have hwsum : ∀ p ∈ initialForest w, p.1 = HTree.wsum w p.2 := by
    intro p hp
    have : p ∈ Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :=
      (initialForest_perm w).mem_iff.mp hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp this
    simp
  obtain ⟨hElems, hCost⟩ := hforest_spec w (initialForest w) T hT hwsum
  refine ⟨T, hT, ?_, ?_⟩
  · refine hElems.trans ?_
    have h1 : ((initialForest w).flatMap (fun p => p.2.elems)).Perm
        ((Finset.univ.toList.map (fun i => (w i, HTree.leaf i))).flatMap
          (fun p => p.2.elems)) := (initialForest_perm w).flatMap_right _
    refine h1.trans ?_
    rw [List.flatMap_map]
    simp
  · -- the cost
    have hzero : ((initialForest w).map (fun p => HTree.tcost w p.2)).sum = 0 := by
      refine List.sum_eq_zero ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have : p ∈ Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :=
        (initialForest_perm w).mem_iff.mp hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp this
      simp
    have hsortEq : (Finset.univ.val.map w).sort (· ≤ ·) = (initialForest w).map Prod.fst := by
      have hcoe : (((initialForest w).map Prod.fst : List ℝ) : Multiset ℝ)
          = Finset.univ.val.map w := by
        have h1 : ((initialForest w : List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι))
            = ((Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :
                List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι)) :=
          Quot.sound (initialForest_perm w)
        calc (((initialForest w).map Prod.fst : List ℝ) : Multiset ℝ)
            = ((initialForest w : List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι)).map Prod.fst := rfl
          _ = ((Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :
                List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι)).map Prod.fst := by rw [h1]
          _ = Finset.univ.val.map w := by
              rw [← Multiset.map_coe, Multiset.map_map, Finset.coe_toList]
              rfl
      rw [← hcoe, sort_coe_of_sorted (initialForest_sorted w)]
    rw [hCost, hzero, Hmul, hsortEq, zero_add]

lemma huffmanCode_eq (w : ι → ℝ) {T : HTree ι} (hT : hforest (initialForest w) = some T) :
    huffmanCode w = HTree.codeOf T := by
  rw [huffmanCode, hT]
  rfl

/-- Huffman's algorithm produces a prefix code. -/
theorem huffmanCode_isPrefixCode (w : ι → ℝ) : IsPrefixCode (huffmanCode w) := by
  rcases List.eq_nil_or_concat (Finset.univ.toList (α := ι)) with hnil | ⟨l, a, hcon⟩
  · intro i j _
    exact absurd (Finset.mem_toList.mpr (Finset.mem_univ i)) (by rw [hnil]; simp)
  · have hne : Finset.univ.toList (α := ι) ≠ [] := by
      rw [hcon]; simp
    obtain ⟨T, hT, hperm, -⟩ := exists_huffman_tree w hne
    have hnd : T.elems.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
    intro i j hij
    rw [huffmanCode_eq w hT]
    refine HTree.codeOf_prefixFree T hnd i ?_ j ?_ hij
    · exact hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ i))
    · exact hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ j))

/-- The expected length of the Huffman code is the value computed by Huffman's algorithm. -/
theorem huffmanCode_expLength (w : ι → ℝ) :
    expLength w (huffmanCode w) = Hmul (Finset.univ.val.map w) := by
  rcases List.eq_nil_or_concat (Finset.univ.toList (α := ι)) with hnil | ⟨l, a, hcon⟩
  · have hempty : (Finset.univ : Finset ι) = ∅ := by
      have : (Finset.univ : Finset ι).val = 0 := by
        rw [← Finset.coe_toList, hnil]; rfl
      exact Finset.val_eq_zero.mp this
    have : (Finset.univ.val.map w) = 0 := by rw [hempty]; rfl
    rw [expLength, this, Hmul_of_card_le_one (by simp)]
    rw [Finset.sum_congr hempty (fun x hx => rfl)]
    simp
  · have hne : Finset.univ.toList (α := ι) ≠ [] := by
      rw [hcon]; simp
    obtain ⟨T, hT, hperm, hcost⟩ := exists_huffman_tree w hne
    have hnd : T.elems.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
    rw [huffmanCode_eq w hT, ← hcost, HTree.tcost_eq_sum_codeOf w T hnd, expLength]
    rw [← Finset.sum_map_toList]
    exact ((hperm.map (fun i => w i * ((HTree.codeOf T i).length : ℝ))).sum_eq).symm

omit [DecidableEq ι] in
/-- Any prefix code has expected length at least the value computed by Huffman's
algorithm. -/
theorem huffman_le_expLength (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ι → List Bool)
    (hc : IsPrefixCode c) : Hmul (Finset.univ.val.map w) ≤ expLength w c := by
  set s : Multiset (ℝ × ℕ) := Finset.univ.val.map (fun i => (w i, (c i).length)) with hs
  have hfst : s.map Prod.fst = Finset.univ.val.map w := by
    rw [hs, Multiset.map_map]
    rfl
  have hcost : mcost s = expLength w c := by
    rw [mcost, hs, Multiset.map_map, expLength, Finset.sum]
    rfl
  have hnn : ∀ p ∈ s, 0 ≤ p.1 := by
    intro p hp
    rw [hs] at hp
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hp
    exact hw i
  have hkraft : mkraft s ≤ 1 := by
    have hL : PFList (Finset.univ.toList.map c) := by
      rw [PFList, List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ ((Finset.nodup_toList (Finset.univ : Finset ι)))
      intro a b _ _ hab
      exact ⟨hc a b hab, hc b a (Ne.symm hab)⟩
    have hk := kraft_inequality _ hL
    have heq : mkraft s = kraftSum (Finset.univ.toList.map c) := by
      rw [mkraft_def, hs, kraftSum, Multiset.map_map, Multiset.map_map]
      rw [← Finset.coe_toList (Finset.univ : Finset ι)]
      rw [List.map_map]
      rfl
    rw [heq]
    exact hk
  have := huffman_le_of_kraft s.card s le_rfl hnn hkraft
  rw [hfst, hcost] at this
  exact this

/-- **Huffman coding is optimal**: the code produced by Huffman's algorithm is a prefix
code, and no prefix code has smaller expected codeword length. -/
theorem huffman_optimal (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    IsPrefixCode (huffmanCode w) ∧
      ∀ c : ι → List Bool, IsPrefixCode c →
        expLength w (huffmanCode w) ≤ expLength w c := by
  refine ⟨huffmanCode_isPrefixCode w, ?_⟩
  intro c hc
  rw [huffmanCode_expLength w]
  exact huffman_le_expLength w hw c hc

end CS

import Mathlib
import RequestProject.Huffman
import RequestProject.Examples

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

#print axioms CS.huffman_optimal

