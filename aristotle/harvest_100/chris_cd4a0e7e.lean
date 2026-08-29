import Mathlib
/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower with core `K`* if any two distinct members
of `S` meet exactly in `K`. -/
def IsSunflower (S : Finset (Finset α)) (K : Finset α) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K

/-- A family of finite sets whose members are pairwise disjoint. -/
def PairwiseDisjointFamily (P : Finset (Finset α)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ≠ B → A ∩ B = ∅

/-- Every finite family `F` contains a maximal (by cardinality) pairwise disjoint subfamily `P`;
maximality implies every nonempty member of `F` meets some member of `P`. -/
theorem exists_maximal_disjoint_subfamily (F : Finset (Finset α)) :
    ∃ P ⊆ F, PairwiseDisjointFamily P ∧
      ∀ A ∈ F, A.Nonempty → ∃ B ∈ P, (A ∩ B).Nonempty := by
  classical
  set PDfams : Finset (Finset (Finset α)) :=
    F.powerset.filter (fun P => PairwiseDisjointFamily P) with hPDfams
  have hne : PDfams.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [hPDfams, PairwiseDisjointFamily]
  obtain ⟨P, hP, hPmax⟩ := Finset.exists_max_image PDfams Finset.card hne
  rw [hPDfams, Finset.mem_filter, Finset.mem_powerset] at hP
  obtain ⟨hPF, hPD⟩ := hP
  refine ⟨P, hPF, hPD, ?_⟩
  intro A hAF hAne
  by_cases hAP : A ∈ P
  · exact ⟨A, hAP, by simpa using hAne⟩
  · by_contra hcon
    push_neg at hcon
    have hdisj : ∀ B ∈ P, A ∩ B = ∅ := hcon
    have hmem : insert A P ∈ PDfams := by
      rw [hPDfams, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hAF hPF, ?_⟩
      intro X hX Y hY hXY
      rcases Finset.mem_insert.1 hX with rfl | hX'
      · rcases Finset.mem_insert.1 hY with rfl | hY'
        · exact absurd rfl hXY
        · exact hdisj Y hY'
      · rcases Finset.mem_insert.1 hY with rfl | hY'
        · rw [Finset.inter_comm]; exact hdisj X hX'
        · exact hPD X hX' Y hY' hXY
    have := hPmax _ hmem
    rw [Finset.card_insert_of_notMem hAP] at this
    omega

/-- The Erdős–Rado sunflower lemma, proved by induction on the uniformity `w`
(auxiliary version, assuming `2 ≤ r`). -/
theorem sunflower_aux (r : ℕ) (hr : 2 ≤ r) :
    ∀ (w : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card = w) →
      Nat.factorial w * (r - 1) ^ w < F.card →
      ∃ S ⊆ F, ∃ K : Finset α, S.card = r ∧ IsSunflower S K := by
  classical
  intro w
  induction w with
  | zero =>
    intro F hF hcard
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      have := hF A hA
      simp [Finset.card_eq_zero.1 this]
    have h2 := Finset.card_le_card hsub
    simp only [Nat.factorial_zero, pow_zero, mul_one, Finset.card_singleton] at hcard h2
    omega
  | succ n ih =>
    intro F hF hcard
    obtain ⟨P, hPF, hPD, hcover⟩ := exists_maximal_disjoint_subfamily F
    by_cases hPr : r ≤ P.card
    · obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hPr
      exact ⟨S, hSP.trans hPF, ∅, hScard, fun A hA B hB hAB =>
        hPD A (hSP hA) B (hSP hB) hAB⟩
    · push_neg at hPr
      set Y : Finset α := P.biUnion id with hYdef
      have hYcard : Y.card ≤ (r - 1) * (n + 1) := by
        have h1 : Y.card ≤ ∑ A ∈ P, (id A).card := Finset.card_biUnion_le
        have h2 : ∑ A ∈ P, (id A).card = P.card * (n + 1) := by
          simp only [id_eq]
          rw [Finset.sum_congr rfl (fun A hA => hF A (hPF hA)), Finset.sum_const,
            smul_eq_mul]
        have : P.card ≤ r - 1 := by omega
        calc Y.card ≤ P.card * (n + 1) := by rw [← h2]; exact h1
          _ ≤ (r - 1) * (n + 1) := Nat.mul_le_mul_right _ this
      have hFsub : F ⊆ Y.biUnion (fun y => F.filter (fun A => y ∈ A)) := by
        intro A hA
        have hAne : A.Nonempty := by
          rw [← Finset.card_pos, hF A hA]; omega
        obtain ⟨B, hB, hAB⟩ := hcover A hA hAne
        obtain ⟨y, hy⟩ := hAB
        rw [Finset.mem_inter] at hy
        refine Finset.mem_biUnion.2 ⟨y, ?_, ?_⟩
        · exact Finset.mem_biUnion.2 ⟨B, hB, hy.2⟩
        · exact Finset.mem_filter.2 ⟨hA, hy.1⟩
      have hFcard : F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card :=
        (Finset.card_le_card hFsub).trans Finset.card_biUnion_le
      have hFpos : 0 < F.card := by omega
      have hYne : Y.Nonempty := by
        rcases Finset.card_pos.1 hFpos with ⟨A, hA⟩
        have hAne : A.Nonempty := by
          rw [← Finset.card_pos, hF A hA]; omega
        obtain ⟨B, hB, hAB⟩ := hcover A hA hAne
        obtain ⟨y, hy⟩ := hAB
        rw [Finset.mem_inter] at hy
        exact ⟨y, Finset.mem_biUnion.2 ⟨B, hB, hy.2⟩⟩
      obtain ⟨y₀, hy₀Y, hy₀max⟩ :=
        Finset.exists_max_image Y (fun y => (F.filter (fun A => y ∈ A)).card) hYne
      set c : ℕ := (F.filter (fun A => y₀ ∈ A)).card with hcdef
      have hsum : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card ≤ Y.card * c :=
        Finset.sum_le_card_nsmul _ _ c (fun y hy => hy₀max y hy)
      have hkey : F.card ≤ (r - 1) * (n + 1) * c :=
        hFcard.trans (hsum.trans (Nat.mul_le_mul_right _ hYcard))
      have hclt : Nat.factorial n * (r - 1) ^ n < c := by
        have hexp : Nat.factorial (n + 1) * (r - 1) ^ (n + 1)
            = (r - 1) * (n + 1) * (Nat.factorial n * (r - 1) ^ n) := by
          rw [Nat.factorial_succ, pow_succ]; ring
        rw [hexp] at hcard
        have hlt : (r - 1) * (n + 1) * (Nat.factorial n * (r - 1) ^ n)
            < (r - 1) * (n + 1) * c := lt_of_lt_of_le hcard hkey
        exact Nat.lt_of_mul_lt_mul_left hlt
      set G : Finset (Finset α) :=
        (F.filter (fun A => y₀ ∈ A)).image (fun A => A.erase y₀) with hGdef
      have hinj : Set.InjOn (fun A => A.erase y₀) (F.filter (fun A => y₀ ∈ A) : Set (Finset α)) := by
        intro A hA B hB hAB
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hA hB
        have := congrArg (insert y₀) hAB
        simpa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] using this
      have hGcard : G.card = c := by
        rw [hGdef, Finset.card_image_of_injOn hinj]
      have hGprop : ∀ B ∈ G, y₀ ∉ B ∧ insert y₀ B ∈ F ∧ B.card = n := by
        intro B hB
        rw [hGdef, Finset.mem_image] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [Finset.mem_filter] at hA
        refine ⟨Finset.notMem_erase _ _, ?_, ?_⟩
        · rw [Finset.insert_erase hA.2]; exact hA.1
        · rw [Finset.card_erase_of_mem hA.2, hF A hA.1]
          omega
      obtain ⟨S', hS'G, K, hS'card, hS'flower⟩ :=
        ih G (fun B hB => (hGprop B hB).2.2) (by rw [hGcard]; exact hclt)
      refine ⟨S'.image (insert y₀), ?_, insert y₀ K, ?_, ?_⟩
      · intro X hX
        rw [Finset.mem_image] at hX
        obtain ⟨B, hB, rfl⟩ := hX
        exact (hGprop B (hS'G hB)).2.1
      · rw [Finset.card_image_of_injOn, hS'card]
        intro A hA B hB hAB
        have hyA : y₀ ∉ A := (hGprop A (hS'G hA)).1
        have hyB : y₀ ∉ B := (hGprop B (hS'G hB)).1
        have := congrArg (fun s => Finset.erase s y₀) hAB
        simpa [Finset.erase_insert hyA, Finset.erase_insert hyB] using this
      · intro X hX Z hZ hXZ
        rw [Finset.mem_image] at hX hZ
        obtain ⟨A, hA, rfl⟩ := hX
        obtain ⟨B, hB, rfl⟩ := hZ
        have hAB : A ≠ B := by
          intro h; exact hXZ (by rw [h])
        have hcore : A ∩ B = K := hS'flower A hA B hB hAB
        ext z
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hz1, hz2⟩
          rcases hz1 with rfl | hz1
          · exact Or.inl rfl
          · rcases hz2 with rfl | hz2
            · exact Or.inl rfl
            · exact Or.inr (by rw [← hcore]; exact Finset.mem_inter.2 ⟨hz1, hz2⟩)
        · rintro (rfl | hz)
          · exact ⟨Or.inl rfl, Or.inl rfl⟩
          · rw [← hcore, Finset.mem_inter] at hz
            exact ⟨Or.inr hz.1, Or.inr hz.2⟩

/-- **Sunflower bound (Erdős–Rado sunflower lemma).**
If `F` is a `w`-uniform family of finite sets with more than `w! * (r-1)^w` members, then `F`
contains a sunflower with `r` petals: a subfamily `S ⊆ F` of exactly `r` sets, together with a
core `K`, such that any two distinct members of `S` intersect exactly in `K`.

Note: the bound proved here is the classical Erdős–Rado bound `w! * (r-1)^w`, not the
asymptotically stronger Alweiss–Lovett–Wu–Zhang bound. -/
theorem sunflower_bound {w r : ℕ} (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = w)
    (hcard : Nat.factorial w * (r - 1) ^ w < F.card) :
    ∃ S ⊆ F, ∃ K : Finset α, S.card = r ∧ IsSunflower S K := by
  classical
  have hFpos : 0 < F.card := by omega
  match r, hcard with
  | 0, _ => exact ⟨∅, Finset.empty_subset _, ∅, rfl, by simp [IsSunflower]⟩
  | 1, _ =>
    obtain ⟨A, hA⟩ := Finset.card_pos.1 hFpos
    exact ⟨{A}, Finset.singleton_subset_iff.2 hA, ∅, Finset.card_singleton _, by
      intro X hX Z hZ hXZ
      rw [Finset.mem_singleton] at hX hZ
      exact absurd (hX.trans hZ.symm) hXZ⟩
  | (r + 2), hcard => exact sunflower_aux (r + 2) (by omega) w F hF hcard

/-- Contrapositive form of the sunflower bound: a `w`-uniform family containing no sunflower
with `r` petals has at most `w! * (r-1)^w` members. -/
theorem card_le_of_no_sunflower {w r : ℕ} (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = w)
    (hno : ¬ ∃ S ⊆ F, ∃ K : Finset α, S.card = r ∧ IsSunflower S K) :
    F.card ≤ Nat.factorial w * (r - 1) ^ w := by
  by_contra h
  exact hno (sunflower_bound F hF (by omega))

end Math2

