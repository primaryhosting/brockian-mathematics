import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

namespace Chem

open Matrix Complex

/-- Adjacency matrix of the cycle graph `C₅` (the Hückel matrix of the cyclopentadienyl
π-system in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

theorem huckel_C5 (μ : ℂ) :
    (∃ v : Fin 5 → ℂ, v ≠ 0 ∧ C5adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 5 ∧ μ = 2 * (Real.cos (2 * Real.pi * k / 5) : ℂ) := by
  constructor
  · rintro h
    -- the eigenvalue equation forces `det (A - μ) = 0`
    have hdet : (C5adj - μ • (1 : Matrix (Fin 5) (Fin 5) ℂ)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨v, hv, hvec⟩ := h
      exact ⟨v, hv, by simp [Matrix.sub_mulVec, hvec, Matrix.smul_mulVec]⟩
    rw [C5adj_det_sub, neg_eq_zero] at hdet
    have hfac : (μ - 2) * (μ ^ 2 + μ - 1) ^ 2 = 0 := by linear_combination hdet
    set s : ℂ := (Real.sqrt 5 : ℂ) with hs
    have h5 : s ^ 2 = 5 := by
      rw [hs]; norm_cast; exact Real.sq_sqrt (by norm_num)
    have hsplit : (μ - 2) * ((μ - (-1 + s) / 2) * (μ - (-1 - s) / 2)) ^ 2 = 0 := by
      have key : (μ - (-1 + s) / 2) * (μ - (-1 - s) / 2) = μ ^ 2 + μ - 1 := by
        linear_combination (-(1 : ℂ) / 4) * h5
      rw [key]; exact hfac
    rcases mul_eq_zero.mp hsplit with h1 | h2
    · refine ⟨0, by norm_num, ?_⟩
      rw [sub_eq_zero.mp h1]
      norm_num
    · have h2' : (μ - (-1 + s) / 2) * (μ - (-1 - s) / 2) = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rcases mul_eq_zero.mp h2' with h3 | h4
      · refine ⟨1, by norm_num, ?_⟩
        have hμ : μ = (-1 + s) / 2 := sub_eq_zero.mp h3
        have harg : 2 * Real.pi * ((1 : ℕ) : ℝ) / 5 = 2 * Real.pi / 5 := by push_cast; ring
        rw [hμ, hs, harg, cos_two_pi_div_five]
        push_cast
        ring
      · refine ⟨2, by norm_num, ?_⟩
        have hμ : μ = (-1 - s) / 2 := sub_eq_zero.mp h4
        have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / 5 = 4 * Real.pi / 5 := by push_cast; ring
        rw [hμ, hs, harg, cos_four_pi_div_five]
        push_cast
        ring
  · rintro ⟨k, -, rfl⟩
    exact C5adj_hasEigenvector k

end Chem

