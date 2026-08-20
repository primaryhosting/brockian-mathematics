import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

theorem hasSum_eta_two : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2) (π ^ 2 / 12) := by
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h; dsimp only at h; omega
  have hev : HasSum (fun n : ℕ => if Even n then (2 : ℝ) / (n : ℝ) ^ 2 else 0) (π ^ 2 / 12) := by
    rw [← Function.Injective.hasSum_iff hinj]
    · have h2 : HasSum (fun k : ℕ => (1 / 2 : ℝ) * (1 / (k : ℝ) ^ 2)) ((1 / 2) * (π ^ 2 / 6)) :=
        hz.mul_left _
      have hval : (1 / 2 : ℝ) * (π ^ 2 / 6) = π ^ 2 / 12 := by ring
      rw [hval] at h2
      refine h2.congr_fun ?_
      intro k
      simp only [Function.comp_def]
      split_ifs with h
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · norm_num
        · have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
          push_cast
          field_simp
      · exact absurd (even_two_mul k) h
    · intro x hx
      simp only [Set.mem_range, not_exists] at hx
      have hodd : ¬ Even x := by
        rintro ⟨r, hr⟩; exact hx r (by omega)
      simp [hodd]
  have hsub := hz.sub hev
  have hval : π ^ 2 / 6 - π ^ 2 / 12 = π ^ 2 / 12 := by ring
  rw [hval] at hsub
  refine hsub.congr_fun ?_
  intro n
  split_ifs with h
  · rw [(h.add_one).neg_one_pow]; ring
  · rw [(Nat.not_even_iff_odd.mp h).add_one.neg_one_pow]; ring

/-- The eta series expansion of the Fermi–Dirac function. -/
