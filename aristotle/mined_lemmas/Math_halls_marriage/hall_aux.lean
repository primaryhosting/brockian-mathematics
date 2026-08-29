import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem hall_aux [Nonempty α] :
    ∀ (n : ℕ) (t : ι → Finset α) (s : Finset ι), s.card ≤ n →
      (∀ u ⊆ s, u.card ≤ (u.biUnion t).card) →
      ∃ f : ι → α, Set.InjOn f ↑s ∧ ∀ i ∈ s, f i ∈ t i := by
  intro n
  induction n with
  | zero =>
      intro t s hs _
      have : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
      subst this
      exact ⟨fun _ => Classical.arbitrary α, by simp, by simp⟩
  | succ n ih =>
      intro t s hs hall
      rcases Nat.lt_or_ge s.card (n + 1) with hlt | hge
      · exact ih t s (Nat.lt_succ_iff.mp hlt) hall
      · have hcard : s.card = n + 1 := le_antisymm hs hge
        by_cases hA : ∀ u ⊆ s, u.Nonempty → u ≠ s → u.card < (u.biUnion t).card
        · -- Case A: every nonempty proper subset expands strictly.
          have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨i₀, hi₀⟩ := hsne
          have h1 : ({i₀} : Finset ι).card ≤ (({i₀} : Finset ι).biUnion t).card :=
            hall _ (by simpa using hi₀)
          rw [Finset.card_singleton, Finset.singleton_biUnion] at h1
          obtain ⟨x, hx⟩ : (t i₀).Nonempty := Finset.card_pos.mp (by omega)
          have hall' : ∀ u ⊆ s.erase i₀, u.card ≤ (u.biUnion fun i => (t i).erase x).card := by
            intro u hu
            rcases u.eq_empty_or_nonempty with rfl | hune
            · simp
            · have hus : u ⊆ s := hu.trans (Finset.erase_subset _ _)
              have hne' : u ≠ s := by
                rintro rfl
                exact (Finset.notMem_erase i₀ u) (hu hi₀)
              have hlt2 := hA u hus hune hne'
              have hpred := Finset.pred_card_le_card_erase (s := u.biUnion t) (a := x)
              rw [biUnion_erase]
              omega
          have hcard' : (s.erase i₀).card ≤ n := by
            have := Finset.card_erase_of_mem hi₀
            omega
          obtain ⟨f', hinj'', hmem''⟩ := ih (fun i => (t i).erase x) _ hcard' hall'
          have hmem' : ∀ i ∈ s.erase i₀, f' i ≠ x ∧ f' i ∈ t i := fun i hi =>
            Finset.mem_erase.mp (hmem'' i hi)
          have hinj' : Set.InjOn f' ↑(s.erase i₀) := hinj''
          refine ⟨Function.update f' i₀ x, ?_, ?_⟩
          · intro a ha b hb hab
            simp only [Finset.mem_coe] at ha hb
            by_cases hai : a = i₀ <;> by_cases hbi : b = i₀
            · rw [hai, hbi]
            · exfalso
              have hb' := hmem' b (Finset.mem_erase.mpr ⟨hbi, hb⟩)
              rw [hai, Function.update_self, Function.update_of_ne hbi] at hab
              exact hb'.1 hab.symm
            · exfalso
              have ha' := hmem' a (Finset.mem_erase.mpr ⟨hai, ha⟩)
              rw [hbi, Function.update_self, Function.update_of_ne hai] at hab
              exact ha'.1 hab
            · simp only [Function.update_of_ne hai, Function.update_of_ne hbi] at hab
              exact hinj' (by simp [ha, hai]) (by simp [hb, hbi]) hab
          · intro i hi
            by_cases hii : i = i₀
            · subst hii; simpa using hx
            · rw [Function.update_of_ne hii]
              exact (hmem' i (Finset.mem_erase.mpr ⟨hii, hi⟩)).2
        · -- Case B: some nonempty proper subset is tight.
          push_neg at hA
          obtain ⟨u, hus, hune, hnes, hle⟩ := hA
          have htight : u.card = (u.biUnion t).card := le_antisymm (hall u hus) hle
          have hucard : u.card ≤ n := by
            have h1 : u.card < s.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hus, hnes⟩)
            omega
          obtain ⟨f₁, hinj₁, hmem₁⟩ := ih t u hucard (fun v hv => hall v (hv.trans hus))
          have hall'' : ∀ v ⊆ s \ u,
              v.card ≤ (v.biUnion fun i => t i \ (u.biUnion t)).card := by
            intro v hv
            have hdisj : Disjoint v u :=
              Finset.disjoint_left.mpr fun a ha hau => (Finset.mem_sdiff.mp (hv ha)).2 hau
            have hkey : (v ∪ u).card ≤ ((v ∪ u).biUnion t).card :=
              hall _ (Finset.union_subset (hv.trans Finset.sdiff_subset) hus)
            have hun : (v ∪ u).biUnion t = (v.biUnion t) ∪ (u.biUnion t) := Finset.union_biUnion
            have hsplit : ((v.biUnion t) ∪ (u.biUnion t)).card
                = ((v.biUnion t) \ (u.biUnion t)).card + (u.biUnion t).card := by
              rw [← Finset.card_union_of_disjoint (Finset.sdiff_disjoint),
                Finset.sdiff_union_self_eq_union]
            rw [hun, hsplit, Finset.card_union_of_disjoint hdisj, ← htight] at hkey
            rw [biUnion_sdiff]
            omega
          have hs''card : (s \ u).card ≤ n := by
            have h1 : (s \ u).card = s.card - u.card := Finset.card_sdiff_of_subset hus
            have h2 : 0 < u.card := Finset.card_pos.mpr hune
            omega
          obtain ⟨f₂, hinj₂', hmem₂'⟩ := ih (fun i => t i \ (u.biUnion t)) _ hs''card hall''
          have hmem₂ : ∀ i ∈ s \ u, f₂ i ∈ t i ∧ f₂ i ∉ u.biUnion t := fun i hi =>
            Finset.mem_sdiff.mp (hmem₂' i hi)
          have hinj₂ : Set.InjOn f₂ ↑(s \ u) := hinj₂'
          refine ⟨fun i => if i ∈ u then f₁ i else f₂ i, ?_, ?_⟩
          · intro a ha b hb hab
            simp only [Finset.mem_coe] at ha hb
            by_cases hau : a ∈ u <;> by_cases hbu : b ∈ u
            · exact hinj₁ (by simpa using hau) (by simpa using hbu)
                (by simpa [hau, hbu] using hab)
            · exfalso
              have h2 := hmem₂ b (Finset.mem_sdiff.mpr ⟨hb, hbu⟩)
              have h1 : f₁ a ∈ u.biUnion t := Finset.mem_biUnion.mpr ⟨a, hau, hmem₁ a hau⟩
              simp only [hau, hbu, if_true, if_false] at hab
              exact h2.2 (hab ▸ h1)
            · exfalso
              have h2 := hmem₂ a (Finset.mem_sdiff.mpr ⟨ha, hau⟩)
              have h1 : f₁ b ∈ u.biUnion t := Finset.mem_biUnion.mpr ⟨b, hbu, hmem₁ b hbu⟩
              simp only [hau, hbu, if_true, if_false] at hab
              exact h2.2 (hab ▸ h1)
            · exact hinj₂ (by simpa using Finset.mem_sdiff.mpr ⟨ha, hau⟩)
                (by simpa using Finset.mem_sdiff.mpr ⟨hb, hbu⟩) (by simpa [hau, hbu] using hab)
          · intro i hi
            by_cases hiu : i ∈ u
            · simpa [hiu] using hmem₁ i hiu
            · simpa [hiu] using (hmem₂ i (Finset.mem_sdiff.mpr ⟨hi, hiu⟩)).1

/-- **Hall's marriage theorem**, combinatorial form: a finite family `t : ι → Finset α` of finite
sets has a system of distinct representatives iff every subfamily of `k` sets covers at least `k`
elements. -/
