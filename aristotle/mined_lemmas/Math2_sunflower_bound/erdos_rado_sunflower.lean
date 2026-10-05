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
