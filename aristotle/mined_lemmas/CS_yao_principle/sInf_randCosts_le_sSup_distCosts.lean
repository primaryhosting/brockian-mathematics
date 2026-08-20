/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A probability distribution on a finite type. -/

theorem sInf_randCosts_le_sSup_distCosts [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    sInf (randCosts c) ≤ sSup (distCosts c) := by
  set t : ℝ := sInf (randCosts c) with ht
  -- separation
  have hdisj : Disjoint (lowBox I t) (domSet c) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨p, hp, hpy⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max y
    have hle : randCost c p ≤ y i0 := ciSup_le fun i => le_trans (hpy i) (hi0 i)
    have hge : t ≤ randCost c p := csInf_le (randCosts_bddBelow c) ⟨p, hp, rfl⟩
    have := hy i0
    linarith
  obtain ⟨f, u, hU, hK⟩ :=
    geometric_hahn_banach_open (convex_lowBox t) (isOpen_lowBox t) (convex_domSet c) hdisj
  set q : I → ℝ := fun i => f (Pi.single i (1 : ℝ)) with hqdef
  have hf : ∀ y : I → ℝ, f y = ∑ i, y i * q i := clm_apply_eq_sum f
  -- the coefficients are nonnegative
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i0
    by_contra hneg
    push_neg at hneg
    set y0 : I → ℝ := fun _ => t - 1 with hy0
    set M : ℝ := |u - f y0| / (-q i0) with hM
    have hMpos : 0 ≤ M := by
      apply div_nonneg (abs_nonneg _)
      linarith
    set y1 : I → ℝ := y0 - M • (Pi.single i0 (1 : ℝ) : I → ℝ) with hy1
    have hy1U : y1 ∈ lowBox I t := by
      intro j
      have : (M • (Pi.single i0 (1 : ℝ) : I → ℝ)) j = if j = i0 then M else 0 := by
        by_cases hj : j = i0 <;> simp [hj]
      simp only [hy1, Pi.sub_apply, hy0, this]
      by_cases hj : j = i0
      · rw [if_pos hj]; linarith
      · rw [if_neg hj]; linarith
    have hfy1 : f y1 = f y0 - M * q i0 := by
      rw [hy1, map_sub, map_smul]
      simp [hqdef, smul_eq_mul]
    have hge : u ≤ f y1 := by
      rw [hfy1]
      have hne : q i0 ≠ 0 := ne_of_lt hneg
      have : M * (-q i0) = |u - f y0| := by
        rw [hM]; field_simp
      nlinarith [le_abs_self (u - f y0)]
    exact absurd (hU y1 hy1U) (not_lt.mpr hge)
  -- the coefficients are not all zero
  have hS : 0 < ∑ i, q i := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun i _ => hq0 i) with h | h
    · exact h
    · exfalso
      have hz : ∀ i, q i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq0 i)).mp h.symm i
          (Finset.mem_univ i)
        exact this
      have hf0 : ∀ y : I → ℝ, f y = 0 := by
        intro y; rw [hf]; simp [hz]
      have h1 : (0 : ℝ) < u := by
        have := hU (fun _ => t - 1) (fun i => by simp)
        rwa [hf0] at this
      have h2 : u ≤ 0 := by
        have := hK _ (domSet_single c (Classical.arbitrary A))
        rwa [hf0] at this
      linarith
  -- `t * ∑ q ≤ u`
  have htu : t * (∑ i, q i) ≤ u := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hmem : (fun _ : I => t - ε / (∑ i, q i)) ∈ lowBox I t := by
      intro i
      have : 0 < ε / (∑ i, q i) := div_pos hε hS
      simp only []
      linarith
    have := hU _ hmem
    rw [hf] at this
    have hsum : ∑ i, (t - ε / (∑ i, q i)) * q i = (t - ε / (∑ i, q i)) * (∑ i, q i) := by
      rw [Finset.mul_sum]
    rw [hsum] at this
    have hne : (∑ i, q i) ≠ 0 := ne_of_gt hS
    have hexp : (t - ε / (∑ i, q i)) * (∑ i, q i) = t * (∑ i, q i) - ε := by
      field_simp
    rw [hexp] at this
    linarith
  -- each pure algorithm has cost at least `t` against the normalized `q`
  have hpure : ∀ a : A, u ≤ ∑ i, c a i * q i := by
    intro a
    have := hK _ (domSet_single c a)
    rwa [hf] at this
  set q' : I → ℝ := fun i => q i / (∑ j, q j) with hq'
  have hq'dist : IsDist q' := by
    constructor
    · intro i; exact div_nonneg (hq0 i) (le_of_lt hS)
    · rw [hq']
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hS)
  have hle : t ≤ distCost c q' := by
    refine le_ciInf fun a => ?_
    have h1 : ∑ i, q' i * c a i = (∑ i, c a i * q i) / (∑ j, q j) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hq']; ring
    rw [h1, le_div_iff₀ hS]
    calc t * (∑ j, q j) ≤ u := htu
      _ ≤ ∑ i, c a i * q i := hpure a
  exact le_trans hle (le_csSup (distCosts_bddAbove c) ⟨q', hq'dist, rfl⟩)

/-- **Yao's minimax principle.**  For a finite set `A` of deterministic algorithms, a finite
set `I` of inputs, and a cost function `c : A → I → ℝ`, the optimal worst-case cost of a
randomized algorithm (a distribution over `A`) equals the optimal distributional complexity
(the best over input distributions of the cost of the best deterministic algorithm):

`inf_{p} sup_{i} E_{a~p} c a i  =  sup_{q} inf_{a} E_{i~q} c a i`. -/
