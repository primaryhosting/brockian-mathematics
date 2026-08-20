import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

theorem multiset_eq_of_powerSum_eq {A B : Multiset ℝ}
    (hA : ∀ x ∈ A, 0 < x) (hB : ∀ x ∈ B, 0 < x)
    (h : ∀ k : ℕ, 1 ≤ k → (A.map (· ^ k)).sum = (B.map (· ^ k)).sum) : A = B := by
  classical
  refine Multiset.ext.mpr fun c => ?_
  set S : Finset ℝ := A.toFinset ∪ B.toFinset with hS
  set d : ℝ → ℝ := fun x => (A.count x : ℝ) - (B.count x : ℝ) with hd
  have hApos : ∀ x ∈ S, (0:ℝ) < x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA x (Multiset.mem_toFinset.mp hx)
    · exact hB x (Multiset.mem_toFinset.mp hx)
  have key : ∀ k : ℕ, 1 ≤ k → ∑ x ∈ S, d x * x ^ k = 0 := by
    intro k hk
    have hAk : (A.map (· ^ k)).sum = ∑ x ∈ S, (A.count x : ℝ) * x ^ k := by
      calc (A.map (· ^ k)).sum = ∑ x ∈ A.toFinset, A.count x • x ^ k :=
            Finset.sum_multiset_map_count A _
        _ = ∑ x ∈ A.toFinset, (A.count x : ℝ) * x ^ k := by simp [nsmul_eq_mul]
        _ = ∑ x ∈ S, (A.count x : ℝ) * x ^ k := by
            refine Finset.sum_subset Finset.subset_union_left ?_
            intro x _ hx
            simp [Multiset.count_eq_zero.mpr (fun hm => hx (Multiset.mem_toFinset.mpr hm))]
    have hBk : (B.map (· ^ k)).sum = ∑ x ∈ S, (B.count x : ℝ) * x ^ k := by
      calc (B.map (· ^ k)).sum = ∑ x ∈ B.toFinset, B.count x • x ^ k :=
            Finset.sum_multiset_map_count B _
        _ = ∑ x ∈ B.toFinset, (B.count x : ℝ) * x ^ k := by simp [nsmul_eq_mul]
        _ = ∑ x ∈ S, (B.count x : ℝ) * x ^ k := by
            refine Finset.sum_subset Finset.subset_union_right ?_
            intro x _ hx
            simp [Multiset.count_eq_zero.mpr (fun hm => hx (Multiset.mem_toFinset.mpr hm))]
    have hk' := h k hk
    rw [hAk, hBk] at hk'
    have hzero : ∑ x ∈ S, ((A.count x : ℝ) * x ^ k - (B.count x : ℝ) * x ^ k) = 0 := by
      rw [Finset.sum_sub_distrib, hk', sub_self]
    rw [← hzero]
    exact Finset.sum_congr rfl fun x _ => by simp [hd]; ring
  have main : ∀ c ∈ S, d c = 0 := by
    intro c hc
    have hc0 : (0:ℝ) < c := hApos c hc
    set p : ℝ[X] := X * ∏ y ∈ S.erase c, (C (c - y)⁻¹ * (X - C y)) with hp
    have hpc : p.eval c = c := by
      rw [hp]
      simp only [eval_mul, eval_X, eval_prod, eval_sub, eval_C]
      rw [Finset.prod_congr rfl (fun y hy => ?_), Finset.prod_const_one, mul_one]
      have : c - y ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hy))
      field_simp
    have hpy : ∀ y ∈ S, y ≠ c → p.eval y = 0 := by
      intro y hy hyc
      rw [hp]
      simp only [eval_mul, eval_prod, eval_sub, eval_C, eval_X]
      have hmem : y ∈ S.erase c := Finset.mem_erase.mpr ⟨hyc, hy⟩
      rw [Finset.prod_eq_zero hmem (by simp)]
      ring
    have hp0 : p.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hp]
      simp
    have hsum : ∑ x ∈ S, d x * p.eval x = 0 := by
      have hrw : ∀ x ∈ S, d x * p.eval x
          = ∑ i ∈ Finset.range (p.natDegree + 1), (d x * p.coeff i) * x ^ i := by
        intro x _
        rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl hrw, Finset.sum_comm]
      refine Finset.sum_eq_zero fun i hi => ?_
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0; simp [hp0]
      · calc ∑ x ∈ S, (d x * p.coeff i) * x ^ i = p.coeff i * ∑ x ∈ S, d x * x ^ i := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
          _ = 0 := by rw [key i hi0, mul_zero]
    have hsingle : ∑ x ∈ S, d x * p.eval x = d c * c := by
      rw [Finset.sum_eq_single c]
      · rw [hpc]
      · intro x hx hxc
        rw [hpy x hx hxc, mul_zero]
      · intro hcS; exact absurd hc hcS
    rw [hsingle] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right (ne_of_gt hc0)
  by_cases hcS : c ∈ S
  · have hdc := main c hcS
    simp only [hd, sub_eq_zero] at hdc
    exact_mod_cast hdc
  · have h1 : A.count c = 0 := Multiset.count_eq_zero.mpr fun hm =>
      hcS (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hm))
    have h2 : B.count c = 0 := Multiset.count_eq_zero.mpr fun hm =>
      hcS (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hm))
    rw [h1, h2]

/-! ### Outer products -/

/-- The rank-one matrix `x yᴴ`. -/
