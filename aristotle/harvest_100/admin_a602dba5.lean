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

/-!
## What is proved here

* `Math2.sunflower_bound` : the sunflower lemma with the classical Erdős–Rado bound, i.e. every
  family of `w`-element sets with more than `w ! * (r-1) ^ w` members contains a sunflower with
  `r` petals.
* `Math2.exists_large_sunflower_free_family` : the factor `(r-1) ^ w` in that bound is necessary,
  since for `r ≥ 2` there is a sunflower-free family of `(r-1) ^ w` sets of size `w`.

The quantitative improvement of Alweiss, Lovett, Wu and Zhang, which replaces the factor `w !` by
`(C * Real.log w) ^ w`, is *not* established here; the bound proved below is the classical one.
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A finite family `S` of finite sets is a *sunflower* if there is a *core* `K` such that any
two distinct members of `S` meet exactly in `K`. -/
def IsSunflower (S : Finset (Finset α)) : Prop :=
  ∃ K : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K

/-- A pairwise disjoint family is a sunflower with empty core. -/
theorem isSunflower_of_pairwise_disjoint {S : Finset (Finset α)}
    (h : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B) : IsSunflower S := by
  refine ⟨∅, fun A hA B hB hAB => ?_⟩
  simpa [Finset.disjoint_iff_inter_eq_empty] using h A hA B hB hAB

/-- Adding a new common element to every member of a sunflower yields a sunflower. -/
theorem IsSunflower.image_insert {S : Finset (Finset α)} {y : α} (hS : IsSunflower S) :
    IsSunflower (S.image (insert y)) := by
  obtain ⟨K, hK⟩ := hS
  refine ⟨insert y K, ?_⟩
  intro A hA B hB hAB
  simp only [Finset.mem_image] at hA hB
  obtain ⟨A', hA', rfl⟩ := hA
  obtain ⟨B', hB', rfl⟩ := hB
  have hne : A' ≠ B' := by
    rintro rfl; exact hAB rfl
  have hinter : Insert.insert y A' ∩ Insert.insert y B' = Insert.insert y (A' ∩ B') := by
    ext z; simp only [Finset.mem_inter, Finset.mem_insert]; tauto
  rw [hinter, hK A' hA' B' hB' hne]

/-- **Erdős–Rado sunflower lemma.**  Any family of `w`-element sets containing more than
`w ! * (r-1)^w` members contains a sunflower with `r` petals. -/
theorem sunflower_bound (w r : ℕ) (F : Finset (Finset α))
    (huniform : ∀ A ∈ F, A.card = w) (hlarge : w ! * (r - 1) ^ w < F.card) :
    ∃ S ⊆ F, S.card = r ∧ IsSunflower S := by
  induction w generalizing F with
  | zero =>
      exfalso
      have hsub : F ⊆ {∅} := by
        intro A hA
        simp only [Finset.mem_singleton]
        exact Finset.card_eq_zero.mp (huniform A hA)
      have hle := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hle
      simp only [Nat.factorial_zero, pow_zero, mul_one] at hlarge
      omega
  | succ w ih =>
      classical
      -- A subfamily of `F` of maximal size consisting of pairwise disjoint sets.
      obtain ⟨M, hMP, hMmax⟩ :=
        Finset.exists_max_image
          (F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B)) Finset.card
          ⟨∅, by simp⟩
      rw [Finset.mem_filter, Finset.mem_powerset] at hMP
      obtain ⟨hMF, hMdisj⟩ := hMP
      by_cases hMr : r ≤ M.card
      · obtain ⟨S, hSM, hScard⟩ := Finset.exists_subset_card_eq hMr
        exact ⟨S, hSM.trans hMF, hScard,
          isSunflower_of_pairwise_disjoint fun A hA B hB h => hMdisj A (hSM hA) B (hSM hB) h⟩
      · push_neg at hMr
        set Y : Finset α := M.biUnion id with hY
        -- `Y` is small.
        have hYcard : Y.card ≤ (r - 1) * (w + 1) := by
          have h1 : Y.card ≤ ∑ A ∈ M, (id A).card := Finset.card_biUnion_le
          have h2 : ∑ A ∈ M, (id A).card = M.card * (w + 1) := by
            simp only [id_eq]
            rw [Finset.sum_congr rfl (fun A hA => huniform A (hMF hA)), Finset.sum_const,
              smul_eq_mul]
          have h3 : M.card ≤ r - 1 := by omega
          calc Y.card ≤ M.card * (w + 1) := h2 ▸ h1
            _ ≤ (r - 1) * (w + 1) := Nat.mul_le_mul_right _ h3
        -- Every member of `F` meets `Y`, by maximality of `M`.
        have hmeet : ∀ A ∈ F, ∃ y ∈ Y, y ∈ A := by
          intro A hA
          by_contra hcon
          push_neg at hcon
          have hdisjAY : ∀ B ∈ M, Disjoint A B := by
            intro B hB
            rw [Finset.disjoint_left]
            intro a haA haB
            exact hcon a (Finset.mem_biUnion.mpr ⟨B, hB, haB⟩) haA
          have hAM : A ∉ M := by
            intro hAM
            have hAne : A.Nonempty := by
              rw [← Finset.card_pos, huniform A hA]; omega
            obtain ⟨a, ha⟩ := hAne
            exact hcon a (Finset.mem_biUnion.mpr ⟨A, hAM, ha⟩) ha
          have hmem : Insert.insert A M ∈
              F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) := by
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨Finset.insert_subset hA hMF, ?_⟩
            intro B hB C hC hBC
            rw [Finset.mem_insert] at hB hC
            rcases hB with rfl | hB
            · rcases hC with rfl | hC
              · exact absurd rfl hBC
              · exact hdisjAY C hC
            · rcases hC with rfl | hC
              · exact (hdisjAY B hB).symm
              · exact hMdisj B hB C hC hBC
          have := hMmax _ hmem
          rw [Finset.card_insert_of_notMem hAM] at this
          omega
        -- Pigeonhole: some point of `Y` lies in many members of `F`.
        have hpop : ∃ y ∈ Y, w ! * (r - 1) ^ w < (F.filter (fun A => y ∈ A)).card := by
          by_contra hcon
          push_neg at hcon
          have hcover : F ⊆ Y.biUnion (fun y => F.filter (fun A => y ∈ A)) := by
            intro A hA
            obtain ⟨y, hyY, hyA⟩ := hmeet A hA
            exact Finset.mem_biUnion.mpr ⟨y, hyY, Finset.mem_filter.mpr ⟨hA, hyA⟩⟩
          have h1 : F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card :=
            le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
          have h2 : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card ≤ Y.card * (w ! * (r - 1) ^ w) := by
            simpa using Finset.sum_le_card_nsmul Y _ _ hcon
          have h3 : Y.card * (w ! * (r - 1) ^ w) ≤ (r - 1) * (w + 1) * (w ! * (r - 1) ^ w) :=
            Nat.mul_le_mul_right _ hYcard
          have h4 : (r - 1) * (w + 1) * (w ! * (r - 1) ^ w) = (w + 1)! * (r - 1) ^ (w + 1) := by
            rw [Nat.factorial_succ, pow_succ]; ring
          omega
        obtain ⟨y, hyY, hy⟩ := hpop
        -- Pass to the link of `y`.
        have hinj : Set.InjOn (fun A : Finset α => A.erase y)
            ((F.filter (fun A => y ∈ A) : Finset (Finset α)) : Set (Finset α)) := by
          intro A hA B hB hAB
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hA hB
          have := congrArg (Insert.insert y) hAB
          simpa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] using this
        set G : Finset (Finset α) := (F.filter (fun A => y ∈ A)).image (fun A => A.erase y) with hG
        have hGcard : w ! * (r - 1) ^ w < G.card := by
          rwa [hG, Finset.card_image_of_injOn hinj]
        have hGuni : ∀ B ∈ G, B.card = w := by
          intro B hB
          rw [hG, Finset.mem_image] at hB
          obtain ⟨A, hA, rfl⟩ := hB
          rw [Finset.mem_filter] at hA
          rw [Finset.card_erase_of_mem hA.2, huniform A hA.1]
          omega
        have hGy : ∀ B ∈ G, y ∉ B := by
          intro B hB
          rw [hG, Finset.mem_image] at hB
          obtain ⟨A, _, rfl⟩ := hB
          exact Finset.notMem_erase y A
        obtain ⟨S', hS'G, hS'card, hS'sun⟩ := ih G hGuni hGcard
        refine ⟨S'.image (Insert.insert y), ?_, ?_, hS'sun.image_insert⟩
        · intro B hB
          rw [Finset.mem_image] at hB
          obtain ⟨B', hB', rfl⟩ := hB
          have := hS'G hB'
          rw [hG, Finset.mem_image] at this
          obtain ⟨A, hA, hAB⟩ := this
          rw [Finset.mem_filter] at hA
          rw [← hAB, Finset.insert_erase hA.2]
          exact hA.1
        · rw [Finset.card_image_of_injOn, hS'card]
          intro A hA B hB hAB
          have hyA : y ∉ A := hGy A (hS'G hA)
          have hyB : y ∉ B := hGy B (hS'G hB)
          have := congrArg (fun s => Finset.erase s y) hAB
          simpa [Finset.erase_insert hyA, Finset.erase_insert hyB] using this

/-- Contrapositive form of the sunflower bound: a `w`-uniform family without a sunflower with
`r` petals has at most `w ! * (r-1) ^ w` members. -/
theorem card_le_of_no_sunflower (w r : ℕ) (F : Finset (Finset α))
    (huniform : ∀ A ∈ F, A.card = w) (hfree : ¬ ∃ S ⊆ F, S.card = r ∧ IsSunflower S) :
    F.card ≤ w ! * (r - 1) ^ w := by
  by_contra hcon
  push_neg at hcon
  exact hfree (sunflower_bound w r F huniform hcon)

/-! ### A matching lower bound

The factor `(r-1)^w` in the sunflower bound cannot be improved: for every `w` and every `r ≥ 2`
there is a family of `(r-1)^w` sets of size `w` containing no sunflower with `r` petals. -/

/-- The graph of a function `f : Fin w → Fin k`, viewed as a `w`-element set of pairs. -/
def graphFinset {w k : ℕ} (f : Fin w → Fin k) : Finset (Fin w × Fin k) :=
  Finset.univ.image (fun i => (i, f i))

theorem mem_graphFinset {w k : ℕ} (f : Fin w → Fin k) (i : Fin w) (v : Fin k) :
    (i, v) ∈ graphFinset f ↔ f i = v := by
  simp only [graphFinset, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨j, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨i, rfl, rfl⟩

theorem card_graphFinset {w k : ℕ} (f : Fin w → Fin k) : (graphFinset f).card = w := by
  rw [graphFinset, Finset.card_image_of_injective _ (fun i j hij => (Prod.mk.injEq .. ▸ hij).1),
    Finset.card_univ, Fintype.card_fin]

theorem graphFinset_injective {w k : ℕ} : Function.Injective (graphFinset (w := w) (k := k)) := by
  intro f g hfg
  funext i
  have h : (i, f i) ∈ graphFinset g := by rw [← hfg]; exact (mem_graphFinset f i (f i)).mpr rfl
  exact ((mem_graphFinset g i (f i)).mp h).symm

/-- **Sharpness of the `(r-1)^w` factor.**  For `r ≥ 2` there is a family of `(r-1)^w` sets of
size `w` that contains no sunflower with `r` petals. -/
theorem exists_large_sunflower_free_family (w r : ℕ) (hr : 2 ≤ r) :
    ∃ F : Finset (Finset (Fin w × Fin (r - 1))),
      (∀ A ∈ F, A.card = w) ∧ F.card = (r - 1) ^ w ∧
        ¬ ∃ S ⊆ F, S.card = r ∧ IsSunflower S := by
  classical
  refine ⟨Finset.univ.image (graphFinset (w := w) (k := r - 1)), ?_, ?_, ?_⟩
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨f, _, rfl⟩ := hA
    exact card_graphFinset f
  · rw [Finset.card_image_of_injective _ graphFinset_injective, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  · rintro ⟨S, hSF, hScard, K, hK⟩
    -- the set of functions whose graph belongs to `S`
    set T : Finset (Fin w → Fin (r - 1)) :=
      Finset.univ.filter (fun f => graphFinset f ∈ S) with hT
    have hTS : T.image graphFinset = S := by
      ext A
      simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨f, hf, rfl⟩; exact hf
      · intro hA
        have := hSF hA
        rw [Finset.mem_image] at this
        obtain ⟨f, _, rfl⟩ := this
        exact ⟨f, hA, rfl⟩
    have hTcard : T.card = r := by
      have himg : (T.image graphFinset).card = T.card :=
        Finset.card_image_of_injective _ graphFinset_injective
      rw [hTS, hScard] at himg
      omega
    -- every coordinate is constant on `T`
    have hconst : ∀ i : Fin w, ∃ v : Fin (r - 1), (i, v) ∈ K := by
      intro i
      have hlt : (Finset.univ : Finset (Fin (r - 1))).card < T.card := by
        rw [hTcard, Finset.card_univ, Fintype.card_fin]; omega
      obtain ⟨f, hf, g, hg, hfg, hval⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
          (fun f _ => Finset.mem_univ (f i))
      refine ⟨f i, ?_⟩
      have hfS : graphFinset f ∈ S := by
        simpa [hT] using hf
      have hgS : graphFinset g ∈ S := by
        simpa [hT] using hg
      have hne : graphFinset f ≠ graphFinset g := fun h => hfg (graphFinset_injective h)
      have := hK _ hfS _ hgS hne
      rw [← this, Finset.mem_inter]
      exact ⟨(mem_graphFinset f i (f i)).mpr rfl, (mem_graphFinset g i (f i)).mpr hval.symm⟩
    -- hence all members of `S` are equal, contradicting `S.card = r ≥ 2`
    have hKsub : ∀ A ∈ S, K ⊆ A := by
      intro A hA
      obtain ⟨B, hB, hBA⟩ : ∃ B ∈ S, B ≠ A := by
        by_contra hcon
        push_neg at hcon
        have : S ⊆ {A} := fun B hB => Finset.mem_singleton.mpr (hcon B hB)
        have := Finset.card_le_card this
        rw [hScard, Finset.card_singleton] at this
        omega
      rw [← hK _ hA _ hB (Ne.symm hBA)]
      exact Finset.inter_subset_left
    have hall : ∀ f ∈ T, ∀ g ∈ T, f = g := by
      intro f hf g hg
      have hfS : graphFinset f ∈ S := by simpa [hT] using hf
      have hgS : graphFinset g ∈ S := by simpa [hT] using hg
      funext i
      obtain ⟨v, hv⟩ := hconst i
      have h1 : f i = v := (mem_graphFinset f i v).mp (hKsub _ hfS hv)
      have h2 : g i = v := (mem_graphFinset g i v).mp (hKsub _ hgS hv)
      rw [h1, h2]
    have hTle : T.card ≤ 1 := Finset.card_le_one.mpr hall
    omega

end Math2

