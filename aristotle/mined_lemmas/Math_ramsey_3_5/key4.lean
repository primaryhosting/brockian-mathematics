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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-! ## Relative (Finset-localized) triangles and independent sets -/

section Rel

variable {V : Type*} [LinearOrder V]

/-- `t` is an independent set of `G`. -/

lemma key4 (G : SimpleGraph V) (s : Finset V) (hs : 9 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G 4 s := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hT0, hI0⟩ := hcon
  obtain ⟨s, hsub, hcard9⟩ := Finset.exists_subset_card_eq hs
  have hT : ¬ HasTriIn G s := fun h => hT0 (mono_tri hsub h)
  have hI : ¬ HasIndepIn G 4 s := fun h => hI0 (mono_indep hsub h)
  -- every vertex of `s` has exactly 3 neighbours inside `s`
  have hdeg : ∀ v ∈ s, (s.filter (fun u => G.Adj v u)).card = 3 := by
    intro v hv
    set N := s.filter (fun u => G.Adj v u) with hNdef
    set M := s.filter (fun u => ¬ G.Adj v u ∧ u ≠ v) with hMdef
    have hunion : N ∪ M = s.erase v := by
      ext u
      simp only [hNdef, hMdef, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro (⟨hu, ha⟩ | ⟨hu, _, hne⟩)
        · exact ⟨fun h => G.irrefl (h ▸ ha), hu⟩
        · exact ⟨hne, hu⟩
      · rintro ⟨hne, hu⟩
        by_cases ha : G.Adj v u
        · exact Or.inl ⟨hu, ha⟩
        · exact Or.inr ⟨hu, ha, hne⟩
    have hdisj : Disjoint N M := by
      rw [Finset.disjoint_left]
      rintro a ha hb
      simp only [hNdef, hMdef, Finset.mem_filter] at ha hb
      exact hb.2.1 ha.2
    have hcards : N.card + M.card = 8 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem hv, hcard9]
    have hNb : N.card ≤ 3 := by
      by_contra hbig
      push_neg at hbig
      obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ N.card by omega)
      refine hI ⟨t, hts.trans (Finset.filter_subset _ _), htc, ?_⟩
      intro x hx y hy hxy hadj
      have hxN := hts hx
      have hyN := hts hy
      simp only [hNdef, Finset.mem_filter] at hxN hyN
      have hvx : G.Adj v x := hxN.2
      have hvy : G.Adj v y := hyN.2
      refine hT ⟨{v, x, y}, ?_, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hv
        · exact hxN.1
        · exact hyN.1
      · have hvx' : v ≠ x := fun h => G.irrefl (h ▸ hvx)
        have hvy' : v ≠ y := fun h => G.irrefl (h ▸ hvy)
        rw [Finset.card_insert_of_notMem (by simp [hvx', hvy']),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      · intro p hp q hq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hpq
            | assumption
            | exact hvx.symm
            | exact hvy.symm
            | exact hadj.symm
    have hMb : M.card < 6 := by
      by_contra hbig
      push_neg at hbig
      rcases key3 G M hbig with h | h
      · exact hT (mono_tri (Finset.filter_subset _ _) h)
      · obtain ⟨t, htM, htc, htind⟩ := h
        have hMnb : ∀ z ∈ t, ¬ G.Adj v z ∧ z ≠ v := by
          intro z hz
          have := htM hz
          simp only [hMdef, Finset.mem_filter] at this
          exact this.2
        have hvt : v ∉ t := fun hvt => (hMnb v hvt).2 rfl
        refine hI ⟨insert v t, ?_, ?_, ?_⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hv
          · exact (Finset.filter_subset _ _) (htM hz)
        · rw [Finset.card_insert_of_notMem hvt, htc]
        · intro x hx y hy hxy
          have hxs := Finset.mem_insert.mp hx
          have hys := Finset.mem_insert.mp hy
          rcases hxs with rfl | hx' <;> rcases hys with rfl | hy'
          · exact absurd rfl hxy
          · exact (hMnb y hy').1
          · exact fun hadj => (hMnb x hx').1 hadj.symm
          · exact htind x hx' y hy' hxy
    omega
  -- double counting the ordered adjacent pairs inside `s`
  set P := (s ×ˢ s).filter (fun p => G.Adj p.1 p.2) with hPdef
  have hP27 : P.card = 27 := by
    rw [hPdef, Finset.card_filter, Finset.sum_product]
    have hsum : ∀ v ∈ s, (∑ u ∈ s, if G.Adj v u then 1 else 0) = 3 := by
      intro v hv
      rw [← Finset.card_filter]
      exact hdeg v hv
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, hcard9]
    simp
  have hswap : (P.filter (fun p => p.1 < p.2)).image Prod.swap
      = P.filter (fun p => ¬ p.1 < p.2) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, hPdef, Finset.mem_product]
    constructor
    · rintro ⟨q, ⟨⟨⟨hq1, hq2⟩, hqadj⟩, hqlt⟩, rfl⟩
      exact ⟨⟨⟨hq2, hq1⟩, hqadj.symm⟩, by simpa using le_of_lt hqlt⟩
    · rintro ⟨⟨⟨hp1, hp2⟩, hpadj⟩, hple⟩
      refine ⟨p.swap, ⟨⟨⟨hp2, hp1⟩, hpadj.symm⟩, ?_⟩, by simp⟩
      have hne : p.1 ≠ p.2 := fun h => G.irrefl (h ▸ hpadj)
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hple) (Ne.symm hne)
  have hhalf : (P.filter (fun p => p.1 < p.2)).card
      + (P.filter (fun p => ¬ p.1 < p.2)).card = P.card :=
    Finset.card_filter_add_card_filter_not _
  rw [← hswap, Finset.card_image_of_injective _ Prod.swap_injective, hP27] at hhalf
  omega

/-- `R(3,5) ≤ 14`. -/
