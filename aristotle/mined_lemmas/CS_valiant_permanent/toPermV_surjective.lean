import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma toPermV_surjective (σ : Equiv.Perm (Vert A)) (hσ : ∀ v, gadget A v (σ v) = 1) :
    ∃ p : (π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i))), toPermV A p.1 p.2 = σ := by
  classical
  have hrow : ∀ i : Fin n, ∃ c : Cells A, σ (Sum.inl i) = Sum.inr c ∧ c.1.1 = i := by
    intro i
    have h := hσ (Sum.inl i)
    rcases hi : σ (Sum.inl i) with j | c
    · rw [hi] at h; simp at h
    · refine ⟨c, rfl, ?_⟩
      rw [hi, gadget_inl_inr] at h
      by_contra hne
      rw [if_neg hne] at h
      exact absurd h (by norm_num)
  choose cf hcf1 hcf2 using hrow
  have hused : ∀ i, σ (Sum.inr (cf i)) = Sum.inl (cf i).1.2 := by
    intro i
    have h := hσ (Sum.inr (cf i))
    rcases hi : σ (Sum.inr (cf i)) with j | c
    · rw [hi, gadget_inr_inl] at h
      by_cases hj : (cf i).1.2 = j
      · exact congrArg Sum.inl hj.symm
      · rw [if_neg hj] at h; exact absurd h (by norm_num)
    · rw [hi, gadget_inr_inr] at h
      by_cases hc : cf i = c
      · exfalso
        have heq : σ (Sum.inl i) = σ (Sum.inr (cf i)) := by rw [hcf1, hi, hc]
        simpa using σ.injective heq
      · rw [if_neg hc] at h; exact absurd h (by norm_num)
  have hinj : Function.Injective (fun i => (cf i).1.2) := by
    intro i i' hii
    have heq : σ (Sum.inr (cf i)) = σ (Sum.inr (cf i')) := by
      rw [hused, hused]; exact congrArg Sum.inl hii
    have h3 : cf i = cf i' := Sum.inr.inj (σ.injective heq)
    rw [← hcf2 i, ← hcf2 i', h3]
  let π' : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (fun i => (cf i).1.2) (Finite.injective_iff_bijective.mp hinj)
  have hπ' : ∀ i, π' i = (cf i).1.2 := fun _ => rfl
  have hA : ∀ i, A (cf i).1.1 (cf i).1.2 = A i (π' i) := by
    intro i; rw [hcf2 i, hπ' i]
  refine ⟨⟨π', fun i => Fin.cast (hA i) (cf i).2⟩, ?_⟩
  have hcell : ∀ i, cellOf A π' (fun i => Fin.cast (hA i) (cf i).2) i = cf i := by
    intro i
    refine Sigma.ext ?_ ?_
    · show (i, π' i) = (cf i).1
      rw [hπ' i]
      exact Prod.ext (hcf2 i).symm rfl
    · exact (Fin.heq_ext_iff (hA i).symm).mpr rfl
  refine Equiv.ext ?_
  rintro (i | c)
  · rw [toPermV_inl, hcell i, hcf1 i]
  · rw [toPermV_inr]
    by_cases h : c = cellOf A π' (fun i => Fin.cast (hA i) (cf i).2) c.1.1
    · rw [if_pos h]
      rw [hcell] at h
      conv_rhs => rw [h]
      rw [hused]
      exact congrArg Sum.inl (congrArg (fun d : Cells A => d.1.2) h)
    · rw [if_neg h]
      rw [hcell] at h
      have h1 := hσ (Sum.inr c)
      rcases hi : σ (Sum.inr c) with j | c'
      · exfalso
        rw [hi, gadget_inr_inl] at h1
        by_cases hj : c.1.2 = j
        · have hex : ∃ i, (cf i).1.2 = c.1.2 := ⟨π'.symm c.1.2, by
            rw [← hπ' (π'.symm c.1.2), Equiv.apply_symm_apply]⟩
          obtain ⟨i, hi2⟩ := hex
          have : σ (Sum.inr (cf i)) = σ (Sum.inr c) := by
            rw [hused, hi, hi2, hj]
          have hcfc : cf i = c := Sum.inr.inj (σ.injective this)
          apply h
          rw [← hcfc, hcf2 i]
        · rw [if_neg hj] at h1; exact absurd h1 (by norm_num)
      · rw [hi, gadget_inr_inr] at h1
        by_cases hc : c = c'
        · exact congrArg Sum.inr hc
        · rw [if_neg hc] at h1; exact absurd h1 (by norm_num)

