/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/
def IsSunflower (S : Finset (Finset α)) (c : Finset α) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = c

/-- `F` contains a sunflower with `r` petals. -/
def HasSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ S ⊆ F, S.card = r ∧ ∃ c, IsSunflower S c

/-- A family of pairwise disjoint sets is a sunflower with empty core. -/
lemma isSunflower_of_pairwiseDisjoint {S : Finset (Finset α)}
    (h : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = ∅) : IsSunflower S ∅ := h

/-- The classical Erdős–Rado sunflower lemma: a family of more than `w! * (r-1)^w` sets of
size `w` contains a sunflower with `r` petals. -/
theorem erdos_rado_sunflower : ∀ (w r : ℕ) (F : Finset (Finset α)), (∀ Y ∈ F, Y.card = w) →
    Nat.factorial w * (r - 1) ^ w < F.card → HasSunflower F r := by
  intro w
  induction w with
  | zero =>
      intro r F hF hcard
      -- every member of `F` is empty, so `F.card ≤ 1`, contradicting `1 < F.card`
      exfalso
      have h1 : F ⊆ {(∅ : Finset α)} := by
        intro Y hY
        have := hF Y hY
        simp only [Finset.card_eq_zero] at this
        simp [this]
      have h2 := Finset.card_le_card h1
      simp only [Finset.card_singleton] at h2
      simp only [Nat.factorial_zero, pow_zero, mul_one] at hcard
      omega
  | succ n ih =>
      intro r F hF hcard
      classical
      have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
      rcases lt_or_ge r 2 with hr | hr
      · -- `r ≤ 1`: trivial sunflowers
        interval_cases r
        · exact ⟨∅, by simp, by simp, ∅, by simp [IsSunflower]⟩
        · obtain ⟨Y, hY⟩ := hFne
          exact ⟨{Y}, by simpa using hY, by simp, ∅, by simp [IsSunflower]⟩
      -- a pairwise disjoint subfamily of maximum size
      set P : Finset (Finset (Finset α)) :=
        F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → A ∩ B = ∅) with hP
      have hPne : P.Nonempty := ⟨∅, by simp [hP]⟩
      obtain ⟨M, hMP, hMmax⟩ := P.exists_max_image Finset.card hPne
      rw [hP, Finset.mem_filter, Finset.mem_powerset] at hMP
      obtain ⟨hMF, hMdisj⟩ := hMP
      rcases le_or_gt r M.card with hMr | hMr
      · -- a large disjoint subfamily is itself a sunflower with empty core
        obtain ⟨S, hSM, hScard⟩ := Finset.exists_subset_card_eq hMr
        exact ⟨S, hSM.trans hMF, hScard, ∅,
          fun A hA B hB hAB => hMdisj A (hSM hA) B (hSM hB) hAB⟩
      -- otherwise all sets meet the small union `T`
      set T : Finset α := M.biUnion id with hT
      have hTcard : T.card ≤ (r - 1) * (n + 1) := by
        calc T.card ≤ ∑ A ∈ M, (id A).card := Finset.card_biUnion_le
          _ = ∑ _A ∈ M, (n + 1) := Finset.sum_congr rfl (fun A hA => hF A (hMF hA))
          _ = M.card * (n + 1) := by simp [Finset.sum_const]
          _ ≤ (r - 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
      have hmeet : ∀ Y ∈ F, ∃ x ∈ T, x ∈ Y := by
        intro Y hY
        by_contra hcon
        push_neg at hcon
        have hYM : Y ∉ M := by
          intro hYM
          have hYsub : Y ⊆ T := fun z hz => Finset.mem_biUnion.mpr ⟨Y, hYM, hz⟩
          have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hF Y hY]; omega)
          obtain ⟨z, hz⟩ := hYne
          exact hcon z (hYsub hz) hz
        have hins : insert Y M ∈ P := by
          rw [hP, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.insert_subset hY hMF, ?_⟩
          intro A hA B hB hAB
          rcases Finset.mem_insert.mp hA with rfl | hA' <;>
            rcases Finset.mem_insert.mp hB with rfl | hB'
          · exact absurd rfl hAB
          · ext z
            simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
            intro hz1 hz2
            exact hcon z (Finset.mem_biUnion.mpr ⟨B, hB', hz2⟩) hz1
          · ext z
            simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
            intro hz1 hz2
            exact hcon z (Finset.mem_biUnion.mpr ⟨A, hA', hz1⟩) hz2
          · exact hMdisj A hA' B hB' hAB
        have hle := hMmax _ hins
        rw [Finset.card_insert_of_notMem hYM] at hle
        omega
      have hTne : T.Nonempty := by
        obtain ⟨Y, hY⟩ := hFne
        obtain ⟨x, hx, -⟩ := hmeet Y hY
        exact ⟨x, hx⟩
      obtain ⟨x, hxT, hxmax⟩ :=
        T.exists_max_image (fun y => (F.filter (fun Y => y ∈ Y)).card) hTne
      have hFle : F.card ≤ T.card * (F.filter (fun Y => x ∈ Y)).card := by
        have hsub : F ⊆ T.biUnion (fun y => F.filter (fun Y => y ∈ Y)) := by
          intro Y hY
          obtain ⟨y, hy, hyY⟩ := hmeet Y hY
          exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨hY, hyY⟩⟩
        calc F.card ≤ (T.biUnion (fun y => F.filter (fun Y => y ∈ Y))).card :=
              Finset.card_le_card hsub
          _ ≤ ∑ y ∈ T, (F.filter (fun Y => y ∈ Y)).card := Finset.card_biUnion_le
          _ ≤ T.card * (F.filter (fun Y => x ∈ Y)).card := by
              simpa [smul_eq_mul] using
                Finset.sum_le_card_nsmul T (fun y => (F.filter (fun Y => y ∈ Y)).card)
                  ((F.filter (fun Y => x ∈ Y)).card) (fun y hy => hxmax y hy)
      -- the link of `x`
      set G : Finset (Finset α) := (F.filter (fun Y => x ∈ Y)).image (fun Y => Y.erase x) with hG
      have hGcard : G.card = (F.filter (fun Y => x ∈ Y)).card := by
        rw [hG]
        refine Finset.card_image_of_injOn ?_
        intro A hA B hB hAB
        simp only [Finset.mem_coe, Finset.mem_filter] at hA hB
        have h : insert x (A.erase x) = insert x (B.erase x) := by
          simp only at hAB
          rw [hAB]
        rwa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] at h
      have hGsize : ∀ Z ∈ G, Z.card = n := by
        intro Z hZ
        rw [hG, Finset.mem_image] at hZ
        obtain ⟨Y, hY, rfl⟩ := hZ
        rw [Finset.mem_filter] at hY
        rw [Finset.card_erase_of_mem hY.2, hF Y hY.1]
        omega
      have hGbound : Nat.factorial n * (r - 1) ^ n < G.card := by
        have key : ((n + 1) * (r - 1)) * (Nat.factorial n * (r - 1) ^ n)
            < ((n + 1) * (r - 1)) * G.card := by
          calc ((n + 1) * (r - 1)) * (Nat.factorial n * (r - 1) ^ n)
              = Nat.factorial (n + 1) * (r - 1) ^ (n + 1) := by
                rw [Nat.factorial_succ]; ring
            _ < F.card := hcard
            _ ≤ T.card * (F.filter (fun Y => x ∈ Y)).card := hFle
            _ ≤ ((n + 1) * (r - 1)) * G.card := by
                rw [hGcard]
                exact Nat.mul_le_mul_right _ (by rw [mul_comm]; exact hTcard)
        exact Nat.lt_of_mul_lt_mul_left key
      obtain ⟨S', hS'G, hS'card, c, hc⟩ := ih r G hGsize hGbound
      have hxnot : ∀ Z ∈ S', x ∉ Z := by
        intro Z hZ
        have := hS'G hZ
        rw [hG, Finset.mem_image] at this
        obtain ⟨Y, -, rfl⟩ := this
        exact Finset.notMem_erase x Y
      refine ⟨S'.image (fun Z => insert x Z), ?_, ?_, insert x c, ?_⟩
      · intro A hA
        rw [Finset.mem_image] at hA
        obtain ⟨Z, hZ, rfl⟩ := hA
        have := hS'G hZ
        rw [hG, Finset.mem_image] at this
        obtain ⟨Y, hY, rfl⟩ := this
        rw [Finset.mem_filter] at hY
        rw [Finset.insert_erase hY.2]
        exact hY.1
      · have hinj : Set.InjOn (fun Z => insert x Z) (S' : Set (Finset α)) := by
          intro A hA B hB hAB
          simp only [Finset.mem_coe] at hA hB
          have h1 : (insert x A).erase x = A := Finset.erase_insert (hxnot A hA)
          have h2 : (insert x B).erase x = B := Finset.erase_insert (hxnot B hB)
          simp only at hAB
          rw [← h1, ← h2, hAB]
        rw [Finset.card_image_of_injOn hinj, hS'card]
      · intro A hA B hB hAB
        rw [Finset.mem_image] at hA hB
        obtain ⟨A', hA', rfl⟩ := hA
        obtain ⟨B', hB', rfl⟩ := hB
        have hne : A' ≠ B' := by
          rintro rfl; exact hAB rfl
        have hins : insert x A' ∩ insert x B' = insert x (A' ∩ B') := by
          ext z; simp only [Finset.mem_inter, Finset.mem_insert]; tauto
        rw [hins, hc A' hA' B' hB' hne]

/-!
## Spread families and the improved (Alweiss–Lovett–Wu–Zhang) bound

We follow the standard modular structure of the modern proofs of the improved sunflower bound
(Alweiss–Lovett–Wu–Zhang, Rao, Frankston–Kahn–Narayanan–Park, Bell–Chueluecha–Warnke):
the combinatorial reduction of the sunflower bound to a *spread* statement, and the spread
statement itself.
-/

/-- `S` is `r`-spread as a family of `k`-element sets: every nonempty set `T` is contained in
at most `r ^ (k - |T|)` members of `S`. -/
def IsSpread (S : Finset (Finset α)) (k : ℕ) (r : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty → ((S.filter (fun A => T ⊆ A)).card : ℝ) ≤ r ^ (k - T.card)

/-- The *spread-to-disjoint* property of a threshold function `rho`: every `rho p k`-spread
family of `k`-sets with at least `(rho p k) ^ k` members contains `p` pairwise disjoint sets. -/
def SpreadDisjoint (rho : ℕ → ℕ → ℝ) : Prop :=
  ∀ (p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ S : Finset (Finset α), (∀ A ∈ S, A.card = k) →
    IsSpread S k (rho p k) → (rho p k) ^ k ≤ (S.card : ℝ) →
    ∃ D ⊆ S, D.card = p ∧ ∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B

/-- A family of at least `p` pairwise disjoint sets is a sunflower with empty core. -/
lemma hasSunflower_of_disjoint {F : Finset (Finset α)} {p : ℕ} {D : Finset (Finset α)}
    (hDF : D ⊆ F) (hD : D.card = p) (hdisj : ∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B) :
    HasSunflower F p :=
  ⟨D, hDF, hD, ∅, fun A hA B hB hAB =>
    Finset.disjoint_iff_inter_eq_empty.mp (hdisj A hA B hB hAB)⟩

/-- **Reduction of the sunflower bound to the spread-to-disjoint property.**
If `rho` is nondecreasing in `k`, at least `p`, and has the spread-to-disjoint property, then
every family of at least `(rho p k) ^ k` sets of size `k` contains a sunflower with `p` petals. -/
theorem sunflower_of_spreadDisjoint {rho : ℕ → ℕ → ℝ}
    (hmono : ∀ p k k' : ℕ, 2 ≤ p → 1 ≤ k' → k' ≤ k → rho p k' ≤ rho p k)
    (hge : ∀ p k : ℕ, 2 ≤ p → 1 ≤ k → (p : ℝ) ≤ rho p k)
    (h : SpreadDisjoint (α := α) rho) :
    ∀ (k p : ℕ), 2 ≤ p → 1 ≤ k → ∀ F : Finset (Finset α), (∀ A ∈ F, A.card = k) →
      (rho p k) ^ k ≤ (F.card : ℝ) → HasSunflower F p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp hk F hF hcard
    have hp0 : (0 : ℝ) < p := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hrho_pos : ∀ m : ℕ, 1 ≤ m → (0 : ℝ) < rho p m := fun m hm =>
      lt_of_lt_of_le hp0 (hge p m hp hm)
    rcases eq_or_lt_of_le hk with hk1 | hk2
    · -- `k = 1`: any `p` distinct singletons are pairwise disjoint
      subst hk1
      have hpF : p ≤ F.card := by
        have : (p : ℝ) ≤ (F.card : ℝ) := by
          calc (p : ℝ) ≤ rho p 1 := hge p 1 hp le_rfl
            _ = (rho p 1) ^ 1 := (pow_one _).symm
            _ ≤ (F.card : ℝ) := hcard
        exact_mod_cast this
      obtain ⟨D, hDF, hDcard⟩ := Finset.exists_subset_card_eq hpF
      refine hasSunflower_of_disjoint hDF hDcard ?_
      intro A hA B hB hAB
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hF A (hDF hA))
      obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (hF B (hDF hB))
      simp only [Finset.disjoint_singleton]
      simpa using hAB
    -- `k ≥ 2`
    by_cases hs : IsSpread F k (rho p k)
    · obtain ⟨D, hDF, hDcard, hdisj⟩ := h p k hp hk F hF hs hcard
      exact hasSunflower_of_disjoint hDF hDcard hdisj
    · -- some nonempty `T` has a large link; induct on the link
      simp only [IsSpread, not_forall, not_le] at hs
      obtain ⟨T, hTne, hTbig⟩ := hs
      have hTk : T.card < k := by
        by_contra hcon
        push_neg at hcon
        have hsub : F.filter (fun A => T ⊆ A) ⊆ {T} := by
          intro A hA
          rw [Finset.mem_filter] at hA
          have : A = T := (Finset.eq_of_subset_of_card_le hA.2 (by
            rw [hF A hA.1]; exact hcon)).symm
          simp [this]
        have h1 : ((F.filter (fun A => T ⊆ A)).card : ℝ) ≤ 1 := by
          have := Finset.card_le_card hsub
          simp only [Finset.card_singleton] at this
          exact_mod_cast this
        have h2 : k - T.card = 0 := by omega
        rw [h2, pow_zero] at hTbig
        linarith
      have hT1 : 1 ≤ T.card := Finset.card_pos.mpr hTne
      obtain ⟨k', hk'⟩ : ∃ k', k' = k - T.card := ⟨k - T.card, rfl⟩
      have hk'1 : 1 ≤ k' := by omega
      have hk'k : k' < k := by omega
      set L : Finset (Finset α) := (F.filter (fun A => T ⊆ A)).image (fun A => A \ T) with hL
      have hLcard : L.card = (F.filter (fun A => T ⊆ A)).card := by
        rw [hL]
        refine Finset.card_image_of_injOn ?_
        intro A hA B hB hAB
        simp only [Finset.mem_coe, Finset.mem_filter] at hA hB
        simp only at hAB
        calc A = A \ T ∪ T := (Finset.sdiff_union_of_subset hA.2).symm
          _ = B \ T ∪ T := by rw [hAB]
          _ = B := Finset.sdiff_union_of_subset hB.2
      have hLsize : ∀ B ∈ L, B.card = k' := by
        intro B hB
        rw [hL, Finset.mem_image] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [Finset.mem_filter] at hA
        rw [Finset.card_sdiff_of_subset hA.2, hF A hA.1, hk']
      have hLbound : (rho p k') ^ k' ≤ (L.card : ℝ) := by
        have h1 : (rho p k') ^ k' ≤ (rho p k) ^ k' :=
          pow_le_pow_left₀ (le_of_lt (hrho_pos k' hk'1)) (hmono p k k' hp hk'1 (le_of_lt hk'k)) k'
        rw [← hk'] at hTbig
        rw [hLcard]
        linarith
      obtain ⟨S', hS'L, hS'card, c, hc⟩ := ih k' hk'k p hp hk'1 L hLsize hLbound
      have hmemF : ∀ B ∈ S', B ∪ T ∈ F := by
        intro B hB
        have := hS'L hB
        rw [hL, Finset.mem_image] at this
        obtain ⟨A, hA, rfl⟩ := this
        rw [Finset.mem_filter] at hA
        rw [Finset.sdiff_union_of_subset hA.2]
        exact hA.1
      have hdisjT : ∀ B ∈ S', Disjoint B T := by
        intro B hB
        have := hS'L hB
        rw [hL, Finset.mem_image] at this
        obtain ⟨A, -, rfl⟩ := this
        exact Finset.sdiff_disjoint
      refine ⟨S'.image (fun B => B ∪ T), ?_, ?_, c ∪ T, ?_⟩
      · intro A hA
        rw [Finset.mem_image] at hA
        obtain ⟨B, hB, rfl⟩ := hA
        exact hmemF B hB
      · rw [Finset.card_image_of_injOn, hS'card]
        intro A hA B hB hAB
        simp only [Finset.mem_coe] at hA hB
        simp only at hAB
        calc A = (A ∪ T) \ T := (Finset.union_sdiff_cancel_right (hdisjT A hA)).symm
          _ = (B ∪ T) \ T := by rw [hAB]
          _ = B := Finset.union_sdiff_cancel_right (hdisjT B hB)
      · intro A hA B hB hAB
        rw [Finset.mem_image] at hA hB
        obtain ⟨A', hA', rfl⟩ := hA
        obtain ⟨B', hB', rfl⟩ := hB
        have hne : A' ≠ B' := by rintro rfl; exact hAB rfl
        have hdist : (A' ∪ T) ∩ (B' ∪ T) = (A' ∩ B') ∪ T := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_union]
          tauto
        rw [hdist, hc A' hA' B' hB' hne]

/-- The elementary greedy bound: the threshold `rho p k = p * k` has the spread-to-disjoint
property. -/
theorem spreadDisjoint_mul : SpreadDisjoint (α := α) (fun p k => (p : ℝ) * k) := by
  intro p k hp hk S hS hspread hcard
  classical
  simp only at hspread hcard
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hr0 : (0 : ℝ) < (p : ℝ) * k := mul_pos hp0 hk0
  have hpow : ((p : ℝ) * k) ^ k = ((p : ℝ) * k) ^ (k - 1) * ((p : ℝ) * k) := by
    rw [← pow_succ]
    congr 1
    omega
  have hdeg : ∀ x : α, ((S.filter (fun A => x ∈ A)).card : ℝ) ≤ ((p : ℝ) * k) ^ (k - 1) := by
    intro x
    have hx := hspread {x} (Finset.singleton_nonempty x)
    simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using hx
  have key : ∀ i : ℕ, i ≤ p →
      ∃ D ⊆ S, D.card = i ∧ ∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨∅, by simp, by simp, by simp⟩
    | succ i ihi =>
      intro hip
      obtain ⟨D, hDS, hDcard, hDdisj⟩ := ihi (by omega)
      have hUcard : ((D.biUnion id).card : ℝ) ≤ (i : ℝ) * k := by
        have h1 : (D.biUnion id).card ≤ ∑ B ∈ D, (id B).card := Finset.card_biUnion_le
        have h2 : ∑ B ∈ D, (id B).card = i * k := by
          have : ∑ B ∈ D, (id B).card = ∑ _B ∈ D, k :=
            Finset.sum_congr rfl (fun B hB => hS B (hDS hB))
          rw [this, Finset.sum_const, hDcard, smul_eq_mul]
        have : (D.biUnion id).card ≤ i * k := by omega
        exact_mod_cast this
      have hex : ∃ A ∈ S, Disjoint A (D.biUnion id) := by
        by_contra hcon
        push_neg at hcon
        have hsub : S ⊆ (D.biUnion id).biUnion (fun x => S.filter (fun A => x ∈ A)) := by
          intro A hA
          obtain ⟨x, hx⟩ := Finset.not_disjoint_iff_nonempty_inter.mp (hcon A hA)
          rw [Finset.mem_inter] at hx
          exact Finset.mem_biUnion.mpr ⟨x, hx.2, Finset.mem_filter.mpr ⟨hA, hx.1⟩⟩
        have h1 : (S.card : ℝ) ≤ ∑ x ∈ D.biUnion id, ((S.filter (fun A => x ∈ A)).card : ℝ) := by
          have hnat : S.card ≤ ∑ x ∈ D.biUnion id, (S.filter (fun A => x ∈ A)).card :=
            le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
          exact_mod_cast hnat
        have h2 : ∑ x ∈ D.biUnion id, ((S.filter (fun A => x ∈ A)).card : ℝ)
            ≤ ((D.biUnion id).card : ℝ) * ((p : ℝ) * k) ^ (k - 1) := by
          calc ∑ x ∈ D.biUnion id, ((S.filter (fun A => x ∈ A)).card : ℝ)
              ≤ ∑ _x ∈ D.biUnion id, ((p : ℝ) * k) ^ (k - 1) :=
                Finset.sum_le_sum (fun x _ => hdeg x)
            _ = ((D.biUnion id).card : ℝ) * ((p : ℝ) * k) ^ (k - 1) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hip' : (i : ℝ) ≤ (p : ℝ) - 1 := by
          have : (i : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hip
          linarith
        have hpk : (0 : ℝ) < ((p : ℝ) * k) ^ (k - 1) := by positivity
        have hfinal : (S.card : ℝ) < ((p : ℝ) * k) ^ k := by
          calc (S.card : ℝ) ≤ ((D.biUnion id).card : ℝ) * ((p : ℝ) * k) ^ (k - 1) :=
                le_trans h1 h2
            _ ≤ ((i : ℝ) * k) * ((p : ℝ) * k) ^ (k - 1) := by
                exact mul_le_mul_of_nonneg_right hUcard (le_of_lt hpk)
            _ ≤ (((p : ℝ) - 1) * k) * ((p : ℝ) * k) ^ (k - 1) := by
                have : (i : ℝ) * k ≤ ((p : ℝ) - 1) * k :=
                  mul_le_mul_of_nonneg_right hip' (le_of_lt hk0)
                exact mul_le_mul_of_nonneg_right this (le_of_lt hpk)
            _ < ((p : ℝ) * k) * ((p : ℝ) * k) ^ (k - 1) := by
                have : (((p : ℝ) - 1) * k) < ((p : ℝ) * k) := by nlinarith
                exact mul_lt_mul_of_pos_right this hpk
            _ = ((p : ℝ) * k) ^ k := by rw [hpow]; ring
        linarith
      obtain ⟨A, hAS, hAU⟩ := hex
      have hAne : A.Nonempty := by
        rw [← Finset.card_pos, hS A hAS]
        omega
      have hAD : A ∉ D := by
        intro hAD
        obtain ⟨z, hz⟩ := hAne
        have hzU : z ∈ D.biUnion id := Finset.mem_biUnion.mpr ⟨A, hAD, hz⟩
        exact (Finset.disjoint_left.mp hAU hz) hzU
      refine ⟨insert A D, Finset.insert_subset hAS hDS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hAD, hDcard]
      · intro X hX Y hY hXY
        have hsubU : ∀ Z ∈ D, Z ⊆ D.biUnion id := fun Z hZ z hz =>
          Finset.mem_biUnion.mpr ⟨Z, hZ, hz⟩
        rcases Finset.mem_insert.mp hX with rfl | hX' <;>
          rcases Finset.mem_insert.mp hY with rfl | hY'
        · exact absurd rfl hXY
        · exact Finset.disjoint_of_subset_right (hsubU Y hY') hAU
        · exact (Finset.disjoint_of_subset_right (hsubU X hX') hAU).symm
        · exact hDdisj X hX' Y hY' hXY
  exact key p le_rfl

/-- The unconditional sunflower bound coming from the greedy spread argument: any family of at
least `(p * k) ^ k` sets of size `k` contains a sunflower with `p` petals. -/
theorem sunflower_bound_greedy (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.card = k) (hcard : ((p : ℝ) * k) ^ k ≤ (F.card : ℝ)) :
    HasSunflower F p := by
  refine sunflower_of_spreadDisjoint (rho := fun p k => (p : ℝ) * k) ?_ ?_ spreadDisjoint_mul
    k p hp hk F hF hcard
  · intro p k k' hp hk' hkk'
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkk'
    exact mul_le_mul_of_nonneg_left this hp0
  · intro p k hp hk
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

/-- The threshold function of the improved sunflower bound: `rhoLog C p k = C * p * log (k+1)`.
(The shift by one only serves to make the function positive at `k = 1`; for `k ≥ 2` we have
`log (k+1) ≤ 2 * log k`, so this is the same bound up to the value of the constant.) -/
noncomputable def rhoLog (C : ℝ) (p k : ℕ) : ℝ := C * p * Real.log (k + 1)

lemma rhoLog_mono (C : ℝ) (hC : 0 ≤ C) (p k k' : ℕ) (hkk' : k' ≤ k) :
    rhoLog C p k' ≤ rhoLog C p k := by
  have h1 : Real.log ((k' : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    have : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkk'
    linarith
  have h2 : (0 : ℝ) ≤ C * p := by positivity
  simpa [rhoLog, mul_assoc] using mul_le_mul_of_nonneg_left h1 h2

lemma le_rhoLog (C : ℝ) (hC : 2 ≤ C) (p k : ℕ) (hk : 1 ≤ k) : (p : ℝ) ≤ rhoLog C p k := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : Real.log 2 ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by norm_num)
    linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have : (1 : ℝ) ≤ C * Real.log ((k : ℝ) + 1) := by nlinarith
  calc (p : ℝ) = (p : ℝ) * 1 := (mul_one _).symm
    _ ≤ (p : ℝ) * (C * Real.log ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left this hp0
    _ = rhoLog C p k := by rw [rhoLog]; ring

/-!
### Random colourings

We encode a uniformly random colouring of a finite ground set `X` by `m` colours as a uniformly
random element of the finite set `X.pi (fun _ => univ)` of functions `∀ a ∈ X, Fin m`.
-/

/-- The `i`-th colour class of the colouring `f` of the ground set `X`. -/
def colorClass (X : Finset α) {m : ℕ} (f : ∀ a ∈ X, Fin m) (i : Fin m) : Finset α :=
  (X.attach.filter (fun a => f a.1 a.2 = i)).image (fun a => a.1)

lemma mem_colorClass {X : Finset α} {m : ℕ} {f : ∀ a ∈ X, Fin m} {i : Fin m} {a : α} :
    a ∈ colorClass X f i ↔ ∃ h : a ∈ X, f a h = i := by
  constructor
  · intro ha
    rw [colorClass, Finset.mem_image] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [Finset.mem_filter] at hb
    obtain ⟨bv, hbX⟩ := b
    subst hba
    exact ⟨hbX, hb.2⟩
  · rintro ⟨h, hf⟩
    rw [colorClass, Finset.mem_image]
    exact ⟨⟨a, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hf⟩, rfl⟩

lemma colorClass_disjoint {X : Finset α} {m : ℕ} {f : ∀ a ∈ X, Fin m} {i j : Fin m} (hij : i ≠ j) :
    Disjoint (colorClass X f i) (colorClass X f j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  obtain ⟨h1, h2⟩ := mem_colorClass.mp hai
  obtain ⟨h3, h4⟩ := mem_colorClass.mp haj
  exact hij (h2 ▸ h4 ▸ rfl)

/-- The set of all colourings of `X` with `m` colours. -/
def colorings (X : Finset α) (m : ℕ) : Finset (∀ a ∈ X, Fin m) :=
  X.pi (fun _ => (Finset.univ : Finset (Fin m)))

/-- **The main technical estimate** of Alweiss–Lovett–Wu–Zhang, Rao and
Bell–Chueluecha–Warnke (Theorem 3 of Bell–Chueluecha–Warnke, with `δ = 1/m` and `ε = 1/2`):
if a family `S` of `k`-element subsets of `X` is `r`-spread with at least `r ^ k` members, where
`r = B * m * log (k+1)`, then for each colour `i`, more than half of all `m`-colourings of `X`
have their `i`-th colour class containing a member of `S`.

This is the one deep ingredient of the improved sunflower bound that is assumed here; everything
else in this file is proved. -/
def ColourEstimate (B : ℝ) : Prop :=
  ∀ (k m : ℕ), 2 ≤ k → 2 ≤ m → ∀ (X : Finset α) (S : Finset (Finset α)),
    (∀ A ∈ S, A ⊆ X) → (∀ A ∈ S, A.card = k) →
    IsSpread S k (B * m * Real.log (k + 1)) →
    (B * m * Real.log (k + 1)) ^ k ≤ (S.card : ℝ) →
    ∀ i : Fin m,
      ((colorings X m).filter (fun f => ∃ A ∈ S, A ⊆ colorClass X f i)).card * 2 >
        (colorings X m).card

/-- From the colour estimate, the spread-to-disjoint property for `rho = 2 B p log (k+1)`:
this is the probabilistic part of the Bell–Chueluecha–Warnke argument (partition the ground set
into `2p` colour classes and use linearity of expectation). -/
theorem spreadDisjoint_of_colourEstimate {B : ℝ} (hB : 1 ≤ B) (h : ColourEstimate (α := α) B) :
    SpreadDisjoint (α := α) (rhoLog (2 * B)) := by
  have hC2 : (2 : ℝ) ≤ 2 * B := by linarith
  intro p k hp hk S hS hspread hcard
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · -- `k = 1`: distinct singletons are pairwise disjoint
    subst hk1
    have hpS : p ≤ S.card := by
      have : (p : ℝ) ≤ (S.card : ℝ) := by
        calc (p : ℝ) ≤ rhoLog (2 * B) p 1 := le_rhoLog _ hC2 p 1 le_rfl
          _ = (rhoLog (2 * B) p 1) ^ 1 := (pow_one _).symm
          _ ≤ (S.card : ℝ) := hcard
      exact_mod_cast this
    obtain ⟨D, hDS, hDcard⟩ := Finset.exists_subset_card_eq hpS
    refine ⟨D, hDS, hDcard, ?_⟩
    intro A hA C hC hAC
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hS A (hDS hA))
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp (hS C (hDS hC))
    simp only [Finset.disjoint_singleton]
    simpa using hAC
  · -- `k ≥ 2`: colour the ground set with `2p` colours
    have hm : 2 ≤ 2 * p := by omega
    have hmpos : 0 < 2 * p := by omega
    have hSX : ∀ A ∈ S, A ⊆ S.biUnion id := fun A hA a ha =>
      Finset.mem_biUnion.mpr ⟨A, hA, ha⟩
    have hrho : B * ((2 * p : ℕ) : ℝ) * Real.log ((k : ℝ) + 1) = rhoLog (2 * B) p k := by
      simp only [rhoLog, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hest := h k (2 * p) hk2 hm (S.biUnion id) S hSX hS
      (by rw [hrho]; exact hspread) (by rw [hrho]; exact hcard)
    -- linearity of expectation over the `2p` colour classes
    set X : Finset α := S.biUnion id with hX
    set P : Finset (∀ a ∈ X, Fin (2 * p)) := colorings X (2 * p) with hP
    have hswap : ∑ i : Fin (2 * p), (P.filter (fun f => ∃ A ∈ S, A ⊆ colorClass X f i)).card
        = ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
            ∃ A ∈ S, A ⊆ colorClass X f i)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hbig : (2 * p) * P.card <
        2 * ∑ i : Fin (2 * p), (P.filter (fun f => ∃ A ∈ S, A ⊆ colorClass X f i)).card := by
      have hne : (Finset.univ : Finset (Fin (2 * p))).Nonempty := by
        refine ⟨⟨0, hmpos⟩, Finset.mem_univ _⟩
      have := Finset.sum_lt_sum_of_nonempty hne
        (fun i _ => hest i)
      simpa [Finset.sum_const, Finset.card_univ, Finset.mul_sum, mul_comm] using this
    -- hence some colouring has more than `p` good colour classes
    have hexf : ∃ f ∈ P, p < (Finset.univ.filter (fun i : Fin (2 * p) =>
        ∃ A ∈ S, A ⊆ colorClass X f i)).card := by
      by_contra hcon
      push_neg at hcon
      have hle : ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
          ∃ A ∈ S, A ⊆ colorClass X f i)).card ≤ P.card * p := by
        simpa [smul_eq_mul] using Finset.sum_le_card_nsmul P _ p hcon
      rw [hswap] at hbig
      have h2 : 2 * ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
          ∃ A ∈ S, A ⊆ colorClass X f i)).card ≤ (2 * p) * P.card := by
        calc 2 * ∑ f ∈ P, (Finset.univ.filter (fun i : Fin (2 * p) =>
                ∃ A ∈ S, A ⊆ colorClass X f i)).card
            ≤ 2 * (P.card * p) := Nat.mul_le_mul_left 2 hle
          _ = (2 * p) * P.card := by ring
      exact absurd hbig (not_lt.mpr h2)
    obtain ⟨f, -, hf⟩ := hexf
    obtain ⟨G, hGsub, hGcard⟩ :=
      Finset.exists_subset_card_eq (le_of_lt hf)
    have hgood : ∀ i ∈ G, ∃ A, A ∈ S ∧ A ⊆ colorClass X f i := by
      intro i hi
      have := hGsub hi
      rw [Finset.mem_filter] at this
      obtain ⟨A, hAS, hAsub⟩ := this.2
      exact ⟨A, hAS, hAsub⟩
    choose g hgS hgsub using hgood
    have hgne : ∀ (i : Fin (2 * p)) (hi : i ∈ G), (g i hi).Nonempty := by
      intro i hi
      rw [← Finset.card_pos, hS _ (hgS i hi)]
      omega
    have hginj : ∀ (i : Fin (2 * p)) (hi : i ∈ G) (j : Fin (2 * p)) (hj : j ∈ G),
        g i hi = g j hj → i = j := by
      intro i hi j hj hij
      by_contra hne
      obtain ⟨a, ha⟩ := hgne i hi
      have h1 : a ∈ colorClass X f i := hgsub i hi ha
      have h2 : a ∈ colorClass X f j := hgsub j hj (hij ▸ ha)
      exact (Finset.disjoint_left.mp (colorClass_disjoint hne) h1) h2
    refine ⟨G.attach.image (fun i => g i.1 i.2), ?_, ?_, ?_⟩
    · intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨i, -, rfl⟩ := hA
      exact hgS i.1 i.2
    · rw [Finset.card_image_of_injOn, Finset.card_attach, hGcard]
      intro i _ j _ hij
      exact Subtype.ext (hginj i.1 i.2 j.1 j.2 hij)
    · intro A hA C hC hAC
      rw [Finset.mem_image] at hA hC
      obtain ⟨i, -, rfl⟩ := hA
      obtain ⟨j, -, rfl⟩ := hC
      have hij : i.1 ≠ j.1 := by
        intro hEq
        apply hAC
        cases i; cases j; subst hEq; rfl
      exact Finset.disjoint_of_subset_left (hgsub i.1 i.2)
        (Finset.disjoint_of_subset_right (hgsub j.1 j.2) (colorClass_disjoint hij))

/-- **The improved sunflower bound of Alweiss–Lovett–Wu–Zhang** (in the sharpened form of
Rao and Bell–Chueluecha–Warnke): there is a constant `C` such that every family of more than
`(C * p * log k) ^ k` sets of size `k` contains a sunflower with `p` petals.

The proof formalised here is the Bell–Chueluecha–Warnke derivation: the combinatorial induction
on `k` reducing the bound to the spread case (`sunflower_of_spreadDisjoint`), together with the
random colouring argument (`spreadDisjoint_of_colourEstimate`). Its single input is the
probabilistic estimate `ColourEstimate B` of Alweiss–Lovett–Wu–Zhang / Rao. -/
theorem sunflower_bound {B : ℝ} (hB : 1 ≤ B) (h : ColourEstimate (α := α) B) :
    ∀ (p k : ℕ), 2 ≤ p → 2 ≤ k → ∀ F : Finset (Finset α), (∀ A ∈ F, A.card = k) →
      ((4 * B) * p * Real.log k) ^ k ≤ (F.card : ℝ) → HasSunflower F p := by
  intro p k hp hk F hF hcard
  have hC0 : (0 : ℝ) ≤ 2 * B := by linarith
  have hC2 : (2 : ℝ) ≤ 2 * B := by linarith
  refine sunflower_of_spreadDisjoint (rho := rhoLog (2 * B))
    (fun p k k' _ _ hkk' => rhoLog_mono _ hC0 p k k' hkk')
    (fun p k hp hk => le_rhoLog _ hC2 p k hk)
    (spreadDisjoint_of_colourEstimate hB h) k p hp (by omega) F hF ?_
  -- `2 B p log (k+1) ≤ 4 B p log k` for `k ≥ 2`
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : 0 < Real.log k := Real.log_pos (by linarith)
  have hstep : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log k := by
    have h1 : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) ^ 2) := by
      apply Real.log_le_log (by linarith)
      nlinarith
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hle : rhoLog (2 * B) p k ≤ (4 * B) * p * Real.log k := by
    have : (2 * B) * p * Real.log ((k : ℝ) + 1) ≤ (2 * B) * p * (2 * Real.log k) := by
      have hnn : (0 : ℝ) ≤ (2 * B) * p := by positivity
      exact mul_le_mul_of_nonneg_left hstep hnn
    calc rhoLog (2 * B) p k = (2 * B) * p * Real.log ((k : ℝ) + 1) := rfl
      _ ≤ (2 * B) * p * (2 * Real.log k) := this
      _ = (4 * B) * p * Real.log k := by ring
  have hnonneg : (0 : ℝ) ≤ rhoLog (2 * B) p k :=
    le_trans (Nat.cast_nonneg p) (le_rhoLog _ hC2 p k (by omega))
  calc (rhoLog (2 * B) p k) ^ k ≤ ((4 * B) * p * Real.log k) ^ k :=
        pow_le_pow_left₀ hnonneg hle k
    _ ≤ (F.card : ℝ) := hcard

end Math2

import Mathlib

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

