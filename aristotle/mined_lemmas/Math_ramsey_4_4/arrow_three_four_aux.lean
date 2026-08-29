/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The two-colour Ramsey number `R(4,4)` equals `18`.

Mathlib (at the pinned revision) contains no theory of Ramsey numbers, so the whole
argument is developed here:

* the classical upper bound `R(p+1,q+1) ≤ R(p,q+1) + R(p+1,q)` (`Math.arrow_step`),
* `R(3,3) ≤ 6` and, via the parity/degree argument, `R(3,4) ≤ 9`
  (`Math.arrow_three_three`, `Math.arrow_three_four`), giving `R(4,4) ≤ 18`,
* the Paley graph on 17 vertices, which has neither a 4-clique nor a 4-element
  independent set, giving `R(4,4) > 17`.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

/-! ## A relation-theoretic formulation of Ramsey's theorem for two colours -/

variable {V : Type*}

/-- A finite set `t` is homogeneous for the relation `r` if all distinct pairs of elements
of `t` are related by `r`. -/

lemma arrow_three_four_aux (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : S.card = 9) : Arrow r S 3 4 := by
  classical
  by_contra hcon
  have hred : ∀ t ⊆ S, t.card = 3 → ¬ Homog r t :=
    fun t hts hc hh => hcon (Or.inl ⟨t, hts, hc, hh⟩)
  have hblue : ∀ t ⊆ S, t.card = 4 → ¬ Homog (fun a b => ¬ r a b) t :=
    fun t hts hc hh => hcon (Or.inr ⟨t, hts, hc, hh⟩)
  have hsymm' : ∀ x y : V, (¬ r x y) → ¬ r y x := fun _ _ h hc => h (hsymm _ _ hc)
  set A : V → Finset V := fun v => (S.erase v).filter (fun u => r v u) with hA
  set B : V → Finset V := fun v => (S.erase v).filter (fun u => ¬ r v u) with hB
  have hAsub : ∀ v, A v ⊆ S := fun v => (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBsub : ∀ v, B v ⊆ S := fun v => (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  -- the neighbourhood of a vertex is anti-homogeneous
  have hindep : ∀ v ∈ S, ∀ x ∈ A v, ∀ y ∈ A v, x ≠ y → ¬ r x y := by
    intro v hv x hx y hy hxy hr
    have hvx : v ≠ x := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1 h.symm
    have hvy : v ≠ y := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1 h.symm
    refine hred {v, x, y} ?_ ?_ (homog_triple hsymm (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hr)
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hv
      · exact hAsub v hx
      · exact hAsub v hy
    · exact Finset.card_eq_three.mpr ⟨v, x, y, hvx, hvy, hxy, rfl⟩
  -- every degree is at most three
  have hdeg_le : ∀ v ∈ S, (A v).card ≤ 3 := by
    intro v hv
    by_contra hgt
    push_neg at hgt
    obtain ⟨t, hts, hct⟩ := Finset.exists_subset_card_eq (show 4 ≤ (A v).card by omega)
    exact hblue t (hts.trans (hAsub v)) hct
      (fun x hx y hy hxy => hindep v hv x (hts hx) y (hts hy) hxy)
  -- every degree is at least three
  have hdeg_ge : ∀ v ∈ S, 3 ≤ (A v).card := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    have hsum : (A v).card + (B v).card = (S.erase v).card :=
      Finset.card_filter_add_card_filter_not _
    have herase : (S.erase v).card = 8 := by rw [Finset.card_erase_of_mem hv, hS]
    have hBcard : 6 ≤ (B v).card := by omega
    rcases arrow_three_three r hsymm (B v) hBcard with ⟨t, hts, hct, hh⟩ | ⟨t, hts, hct, hh⟩
    · exact hred t (hts.trans (hBsub v)) hct hh
    · have hvt : v ∉ t := fun hvt =>
        (Finset.mem_erase.mp (Finset.mem_filter.mp (hts hvt)).1).1 rfl
      refine hblue (insert v t) ?_ ?_ (homog_insert hsymm' hh
        (fun u hu => (Finset.mem_filter.mp (hts hu)).2))
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hv
        · exact hBsub v (hts h)
      · rw [Finset.card_insert_of_notMem hvt, hct]
  have hdeg : ∀ v ∈ S, (A v).card = 3 := fun v hv => le_antisymm (hdeg_le v hv) (hdeg_ge v hv)
  -- the degree sum is both `27` and even
  set f : V → V → ℕ := fun a b => if a ≠ b ∧ r a b then 1 else 0 with hf
  have hfsymm : ∀ a b, f a b = f b a := by
    intro a b
    by_cases h : a ≠ b ∧ r a b
    · have h' : b ≠ a ∧ r b a := ⟨Ne.symm h.1, hsymm _ _ h.2⟩
      simp only [hf, if_pos h, if_pos h']
    · have h' : ¬ (b ≠ a ∧ r b a) := fun hc => h ⟨Ne.symm hc.1, hsymm _ _ hc.2⟩
      simp only [hf, if_neg h, if_neg h']
  have hfd : ∀ a, f a a = 0 := by
    intro a
    simp only [hf, ne_eq, not_true_eq_false, false_and, if_false]
  have hcardf : ∀ v ∈ S, (A v).card = ∑ u ∈ S, f v u := by
    intro v _
    have hAv : A v = S.filter (fun u => v ≠ u ∧ r v u) := by
      ext u
      simp only [hA, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hu⟩, hr⟩; exact ⟨hu, ⟨Ne.symm hne, hr⟩⟩
      · rintro ⟨hu, hne, hr⟩; exact ⟨⟨Ne.symm hne, hu⟩, hr⟩
    rw [hAv, Finset.card_filter]
  have h27 : ∑ v ∈ S, ∑ u ∈ S, f v u = 27 := by
    rw [← Finset.sum_congr rfl hcardf, Finset.sum_congr rfl hdeg]
    simp [hS]
  have hev := even_sum_pairs f hfsymm hfd S
  rw [h27] at hev
  obtain ⟨k, hk⟩ := hev
  omega

/-- `R(3,4) ≤ 9`. -/
