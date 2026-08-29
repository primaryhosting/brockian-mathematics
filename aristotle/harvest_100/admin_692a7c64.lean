import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/
def RelativelyLarge (Y : Finset ℕ) : Prop :=
  ∃ a ∈ Y, (∀ b ∈ Y, a ≤ b) ∧ a ≤ Y.card

/-- `Y` is homogeneous for the colouring `c` of `k`-element sets: all `k`-element subsets of
`Y` receive the same colour. -/
def IsHomog (k : ℕ) {r : ℕ} (c : Finset ℕ → Fin r) (Y : Finset ℕ) : Prop :=
  ∀ s ⊆ Y, s.card = k → ∀ t ⊆ Y, t.card = k → c s = c t

/-! ## Ultrafilter limits of finitely valued functions -/

theorem exists_ulim {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) :
    ∃ j : Fin r, {x | f x = j} ∈ U := by
  have h : (⋃ j ∈ (Set.univ : Set (Fin r)), {x | f x = j}) ∈ U := by
    have hu : (⋃ j ∈ (Set.univ : Set (Fin r)), {x | f x = j}) = Set.univ := by
      ext x; simp
    rw [hu]; exact Filter.univ_mem
  obtain ⟨j, -, hj⟩ := (Ultrafilter.finite_biUnion_mem_iff Set.finite_univ).1 h
  exact ⟨j, hj⟩

/-- The `U`-limit of a function with values in a finite type. -/
noncomputable def ulim {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) : Fin r :=
  (exists_ulim U f).choose

theorem ulim_spec {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) :
    {x | f x = ulim U f} ∈ U :=
  (exists_ulim U f).choose_spec

/-! ## The infinite Ramsey theorem

We fix a family `D` of colourings, where `D i` colours the `(k - i)`-element sets, obtained by
iterating the ultrafilter-limit operation. -/

/-- The set of admissible next elements after having chosen the finite set `T`. -/
def goodSet {r : ℕ} (D : ℕ → Finset ℕ → Fin r) (k : ℕ) (T : Finset ℕ) : Set ℕ :=
  {x | (∀ y ∈ T, y < x) ∧ ∀ s ⊆ T, ∀ i, i + s.card + 1 = k → D i (insert x s) = D (i + 1) s}

theorem goodSet_mem {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite)
    (hD : ∀ i s, D (i + 1) s = ulim U (fun x => D i (insert x s))) (T : Finset ℕ) :
    goodSet D k T ∈ U := by
  have h1 : {x | ∀ y ∈ T, y < x} ∈ U := by
    apply hU
    rw [Filter.mem_cofinite]
    refine Set.Finite.subset (Set.finite_Iic (T.sup id)) ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact le_trans hxy (Finset.le_sup (f := id) hy)
  have h2 : (⋂ s ∈ T.powerset,
      {x | ∀ i, i + s.card + 1 = k → D i (insert x s) = D (i + 1) s}) ∈ U := by
    refine (Filter.biInter_finset_mem _).2 ?_
    intro s _
    by_cases hcard : s.card + 1 ≤ k
    · refine Filter.mem_of_superset (ulim_spec U (fun x => D (k - s.card - 1) (insert x s))) ?_
      intro x hx i hi
      have hik : i = k - s.card - 1 := by omega
      subst hik
      rw [hD _ s]
      exact hx
    · exact Filter.univ_mem' (fun _ _ hi => absurd hi (by omega))
  filter_upwards [h1, h2] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  intro s hsT i hi
  exact (Set.mem_iInter₂.1 hx2 s (Finset.mem_powerset.2 hsT)) i hi

/-- The finite set built after `n` steps of the greedy construction. -/
noncomputable def chain {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ) :
    ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (sInf (goodSet D k (chain U D k n))) (chain U D k n)

/-- The `n`-th element chosen by the greedy construction. -/
noncomputable def chainElt {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ)
    (n : ℕ) : ℕ := sInf (goodSet D k (chain U D k n))

theorem chain_succ {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k n : ℕ) :
    chain U D k (n + 1) = insert (chainElt U D k n) (chain U D k n) := rfl

section Greedy

variable {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ)
  (hU : (U : Filter ℕ) ≤ cofinite)
  (hD : ∀ i s, D (i + 1) s = ulim U (fun x => D i (insert x s)))

include hU hD

theorem chainElt_mem_goodSet (n : ℕ) :
    chainElt U D k n ∈ goodSet D k (chain U D k n) :=
  Nat.sInf_mem (Ultrafilter.nonempty_of_mem (goodSet_mem U D k hU hD _))

theorem lt_chainElt (n : ℕ) : ∀ y ∈ chain U D k n, y < chainElt U D k n :=
  (chainElt_mem_goodSet U D k hU hD n).1

theorem chainElt_lt_succ (n : ℕ) : chainElt U D k n < chainElt U D k (n + 1) := by
  refine lt_chainElt U D k hU hD (n + 1) _ ?_
  rw [chain_succ]
  exact Finset.mem_insert_self _ _

theorem chainElt_strictMono : StrictMono (chainElt U D k) :=
  strictMono_nat_of_lt_succ (chainElt_lt_succ U D k hU hD)

omit hU hD in
theorem chain_eq_image (n : ℕ) :
    chain U D k n = (Finset.range n).image (chainElt U D k) := by
  induction n with
  | zero => simp [chain]
  | succ n ih => rw [chain_succ, ih, Finset.range_add_one, Finset.image_insert]

/-- Every `j`-element subset of the constructed set gets the colour `D k ∅`
(with the appropriate index `i`, where `i + j = k`). -/
theorem homog_aux : ∀ (n : ℕ) (s : Finset ℕ), s.card = n → ↑s ⊆ Set.range (chainElt U D k) →
    ∀ i, i + n = k → D i s = D k ∅ := by
  intro n
  induction n with
  | zero =>
      intro s hs0 _ i hi
      rw [Finset.card_eq_zero] at hs0
      subst hs0
      simp only [Nat.add_zero] at hi
      subst hi
      rfl
  | succ n ih =>
      intro s hsc hs i hi
      have hne : s.Nonempty := Finset.card_pos.1 (by omega)
      set x := s.max' hne with hxdef
      have hxs : x ∈ s := s.max'_mem hne
      obtain ⟨p, hp⟩ : x ∈ Set.range (chainElt U D k) := hs hxs
      have hcard : (s.erase x).card = n := by
        rw [Finset.card_erase_of_mem hxs, hsc]
        omega
      have hsub : s.erase x ⊆ chain U D k p := by
        intro y hy
        have hys : y ∈ s := Finset.mem_of_mem_erase hy
        have hyne : y ≠ x := Finset.ne_of_mem_erase hy
        obtain ⟨q, hq⟩ : y ∈ Set.range (chainElt U D k) := hs hys
        have hylt : y < x := lt_of_le_of_ne (s.le_max' y hys) hyne
        have hqp : q < p := by
          rw [← hq, ← hp] at hylt
          exact (chainElt_strictMono U D k hU hD).lt_iff_lt.1 hylt
        rw [chain_eq_image U D k p]
        exact Finset.mem_image.2 ⟨q, Finset.mem_range.2 hqp, hq⟩
      have key := (chainElt_mem_goodSet U D k hU hD p).2 (s.erase x) hsub i (by omega)
      rw [hp, Finset.insert_erase hxs] at key
      rw [key]
      refine ih (s.erase x) hcard ?_ (i + 1) (by omega)
      exact fun y hy => hs (Finset.mem_of_mem_erase hy)

end Greedy

/-- **Infinite Ramsey theorem**: for every colouring of the `k`-element subsets of `ℕ` with
`r` colours there is an infinite homogeneous set. -/
theorem infinite_ramsey (k r : ℕ) (c : Finset ℕ → Fin r) :
    ∃ H : Set ℕ, H.Infinite ∧ ∃ j : Fin r, ∀ s : Finset ℕ, ↑s ⊆ H → s.card = k → c s = j := by
  classical
  let U : Ultrafilter ℕ := hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ cofinite := hyperfilter_le_cofinite
  let D : ℕ → Finset ℕ → Fin r :=
    fun i => (fun (D' : Finset ℕ → Fin r) (s : Finset ℕ) => ulim U (fun x => D' (insert x s)))^[i] c
  have hD : ∀ i s, D (i + 1) s = ulim U (fun x => D i (insert x s)) := by
    intro i s
    show ((fun (D' : Finset ℕ → Fin r) (s : Finset ℕ) =>
        ulim U (fun x => D' (insert x s)))^[i + 1] c) s = _
    rw [Function.iterate_succ_apply']
  have hD0 : D 0 = c := rfl
  refine ⟨Set.range (chainElt U D k), ?_, D k ∅, ?_⟩
  · exact Set.infinite_range_of_injective (chainElt_strictMono U D k hU hD).injective
  · intro s hsub hcard
    have := homog_aux U D k hU hD s.card s rfl hsub 0 (by omega)
    rw [hD0] at this
    exact this

/-! ## The Paris–Harrington theorem -/

/-- **Paris–Harrington (strengthened finite Ramsey theorem)**: for all `k`, `r`, `m` there is
`N` such that every `r`-colouring of the `k`-element subsets of `{1, …, N}` admits a
homogeneous set `Y` with at least `m` elements which is moreover *relatively large*
(`Y.card ≥ min Y`).

The statement is true — that is what is proved here, using the infinite Ramsey theorem together
with a compactness (ultrafilter limit) argument — while it is famously *not* provable in
first-order Peano arithmetic; that metamathematical half is a statement about the proof system
PA and is not formalized here. -/
theorem Paris_Harrington (k r m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin r,
      ∃ Y ⊆ Finset.Icc 1 N, IsHomog k c Y ∧ m ≤ Y.card ∧ RelativelyLarge Y := by
  classical
  by_contra hcon
  push_neg at hcon
  choose cN hcN using hcon
  let U : Ultrafilter ℕ := hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ cofinite := hyperfilter_le_cofinite
  let cinf : Finset ℕ → Fin r := fun s => ulim U (fun N => cN N s)
  obtain ⟨H, hHinf, j, hj⟩ := infinite_ramsey k r cinf
  have hH1 : (H \ {0}).Infinite := hHinf.diff (Set.finite_singleton 0)
  have hne : (H \ {0}).Nonempty := hH1.nonempty
  set a := sInf (H \ {0}) with ha
  have hamem : a ∈ H \ {0} := Nat.sInf_mem hne
  have hamin : ∀ b ∈ H \ {0}, a ≤ b := fun b hb => Nat.sInf_le hb
  obtain ⟨T, hT, hTcard⟩ := (hH1.diff (Set.finite_singleton a)).exists_subset_card_eq (max m a)
  have haT : a ∉ T := fun h => (hT h).2 rfl
  set Y : Finset ℕ := insert a T with hY
  have hYcard : Y.card = max m a + 1 := by
    rw [hY, Finset.card_insert_of_notMem haT, hTcard]
  have hTH : ∀ y ∈ T, y ∈ H \ {0} := fun y hy => (hT hy).1
  have hYH : ∀ y ∈ Y, y ∈ H \ {0} := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hamem
    · exact hTH y hy
  have hYmin : ∀ b ∈ Y, a ≤ b := fun b hb => hamin b (hYH b hb)
  have hS1 : (⋂ s ∈ Y.powersetCard k, {N | cN N s = cinf s}) ∈ U := by
    refine (Filter.biInter_finset_mem _).2 ?_
    intro s _
    exact ulim_spec U (fun N => cN N s)
  have hS2 : {N | ∀ y ∈ Y, y ≤ N} ∈ U := by
    apply hU
    rw [Filter.mem_cofinite]
    refine Set.Finite.subset (Set.finite_Iio (Y.sup id)) ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact lt_of_lt_of_le hxy (Finset.le_sup (f := id) hy)
  obtain ⟨N, hN1, hN2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hS1 hS2)
  have hYsub : Y ⊆ Finset.Icc 1 N := by
    intro y hy
    refine Finset.mem_Icc.2 ⟨?_, hN2 y hy⟩
    have hy0 := (hYH y hy).2
    simp only [Set.mem_singleton_iff] at hy0
    omega
  have hHomog : IsHomog k (cN N) Y := by
    intro s hs hsc t ht htc
    have hsmem : s ∈ Y.powersetCard k := Finset.mem_powersetCard.2 ⟨hs, hsc⟩
    have htmem : t ∈ Y.powersetCard k := Finset.mem_powersetCard.2 ⟨ht, htc⟩
    have hs' : cN N s = cinf s := Set.mem_iInter₂.1 hN1 s hsmem
    have ht' : cN N t = cinf t := Set.mem_iInter₂.1 hN1 t htmem
    have hsj : cinf s = j := hj s (fun y hy => (hYH y (hs hy)).1) hsc
    have htj : cinf t = j := hj t (fun y hy => (hYH y (ht hy)).1) htc
    rw [hs', ht', hsj, htj]
  have hmcard : m ≤ Y.card := by rw [hYcard]; omega
  have hlarge : RelativelyLarge Y := by
    refine ⟨a, Finset.mem_insert_self _ _, hYmin, ?_⟩
    rw [hYcard]; omega
  exact hcN N Y hYsub hHomog hmcard hlarge

end Frontier

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

