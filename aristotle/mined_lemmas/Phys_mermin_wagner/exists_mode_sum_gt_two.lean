/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real

namespace Phys

/-- The spin-wave (harmonic) energy of the Fourier mode `j` of a nearest-neighbour
model on the `d`-dimensional discrete torus with `L` sites per side, in units where
the coupling constant is `1`.  The momentum attached to the mode `j` has components
`k i = 2π * j i / L`, and the lattice dispersion relation is
`ε k = ∑ i, 2 * (1 - cos (k i))`. -/

lemma exists_mode_sum_gt_two (B : ℝ) :
    ∃ (L : ℕ) (D : Finset (Fin 2 → Fin L)),
      (∀ j ∈ D, ∃ i, (j i : ℕ) ≠ 0) ∧
      B * (L : ℝ) ^ (2 : ℕ) < ∑ j ∈ D, 1 / modeSq 2 L j := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 8 * π ^ 2 * B < ∑ i ∈ Finset.range N, 1 / ((i:ℝ) + 1) :=
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (8 * π ^ 2 * B)).exists
  refine ⟨N + 1,
    Finset.univ.filter (fun j : Fin 2 → Fin (N+1) => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)),
    ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_filter] at hj
    exact ⟨0, by omega⟩
  · set L : ℕ := N + 1 with hLdef
    have hLR : (0:ℝ) < (L:ℝ) := by positivity
    have hpt : ∀ j ∈ Finset.univ.filter
        (fun j : Fin 2 → Fin L => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)),
        (L:ℝ)^2 / (8 * π^2) * (1 / ((j 1 : ℕ):ℝ)^2) ≤ 1 / modeSq 2 L j := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨h0, h1⟩ := hj
      have hb : (0:ℝ) < ((j 1 : ℕ):ℝ) := by
        have : 0 < (j 1 : ℕ) := lt_of_lt_of_le h0 h1
        exact_mod_cast this
      have ha : (0:ℝ) ≤ ((j 0 : ℕ):ℝ) := by positivity
      have hab : ((j 0 : ℕ):ℝ) ≤ ((j 1 : ℕ):ℝ) := by exact_mod_cast h1
      have hQpos : 0 < modeSq 2 L j := modeSq_pos ⟨0, by omega⟩
      have ha2 : ((j 0 : ℕ):ℝ)^2 ≤ ((j 1 : ℕ):ℝ)^2 := by nlinarith
      have hQle : modeSq 2 L j ≤ 8 * π^2 * ((j 1 : ℕ):ℝ)^2 / (L:ℝ)^2 := by
        rw [modeSq, Fin.sum_univ_two, div_pow, div_pow, ← add_div,
          div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [Real.pi_pos, sq_nonneg π, mul_le_mul_of_nonneg_left ha2 (sq_nonneg π)]
      have hfin := one_div_le_one_div_of_le hQpos hQle
      calc (L:ℝ)^2 / (8 * π^2) * (1 / ((j 1 : ℕ):ℝ)^2)
          = 1 / (8 * π^2 * ((j 1 : ℕ):ℝ)^2 / (L:ℝ)^2) := by
            rw [one_div_div]; field_simp
        _ ≤ 1 / modeSq 2 L j := hfin
    refine lt_of_lt_of_le ?_ (Finset.sum_le_sum hpt)
    have hcomp : ∑ j ∈ Finset.univ.filter
        (fun j : Fin 2 → Fin L => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)),
        (L:ℝ)^2 / (8 * π^2) * (1 / ((j 1 : ℕ):ℝ)^2)
        = (L:ℝ)^2 / (8 * π^2) * ∑ i ∈ Finset.range N, 1 / ((i:ℝ) + 1) := by
      rw [sum_filter_tri]
      have hb : ∀ b : Fin L, ∑ a : Fin L,
          (if 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ) then
            (L:ℝ)^2 / (8 * π^2) * (1 / (((![a, b] : Fin 2 → Fin L) 1 : ℕ):ℝ)^2) else 0)
          = (L:ℝ)^2 / (8 * π^2) * (1 / ((b:ℕ):ℝ)) := by
        intro b
        have hsimp : ∀ a : Fin L, (((![a, b] : Fin 2 → Fin L) 1 : ℕ):ℝ) = ((b:ℕ):ℝ) := by
          intro a; simp
        simp only [hsimp]
        rw [sum_ite_Ioc]
        rcases Nat.eq_zero_or_pos (b:ℕ) with h | h
        · simp [h]
        · have hbne : ((b:ℕ):ℝ) ≠ 0 := by positivity
          field_simp
      simp only [hb]
      rw [← Finset.mul_sum]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i => 1 / ((i:ℕ):ℝ)) L, hLdef, Finset.sum_range_succ']
      simp
    rw [hcomp, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hN (show (0:ℝ) < (L:ℝ)^2 by positivity)
    linarith

/-- Infrared divergence in dimension `d ≤ 2`: the sum of `|k|⁻²` over a set of
nonzero modes can be made arbitrarily large compared with the volume `L ^ d`. -/
