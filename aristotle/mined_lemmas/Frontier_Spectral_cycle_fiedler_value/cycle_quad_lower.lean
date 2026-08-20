/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma cycle_quad_lower (x : ZMod (m + 3) → ℝ) (hsum : ∑ j : ZMod (m + 3), x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) * (∑ j : ZMod (m + 3), (x j) ^ 2)
      ≤ ∑ j : ZMod (m + 3), (x j - x (j + 1)) ^ 2 := by
  have hNpos : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  -- the discrete Fourier coefficients of `x`
  have h1 : ∑ k : ZMod (m + 3), normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k))
      = ((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j) ^ 2 := by
    have h := parseval (N := m + 3) (fun j => ((x j : ℝ) : ℂ))
    simpa [Complex.normSq_ofReal, sq] using h
  have hX0 : (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * 0)) = 0 := by
    simp only [mul_zero, chi_zero, mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_zero]
  have h3 : normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * 0)) = 0 := by
    rw [hX0, map_zero]
  have hterm : ∀ k : ZMod (m + 3),
      normSq (∑ j : ZMod (m + 3), ((x j - x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k))
        = (2 - 2 * (chi (m + 3) k).re) *
            normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)) := by
    intro k
    have hsplit : ∑ j : ZMod (m + 3), ((x j - x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k)
        = (1 - chi (m + 3) (-k)) * ∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k) := by
      have hpt : ∀ j : ZMod (m + 3), ((x j - x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k)
          = ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)
            - ((x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k) := by
        intro j; push_cast; ring
      rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib,
        sum_shift_chi (fun j => ((x j : ℝ) : ℂ)) k]
      ring
    have hre : (chi (m + 3) (-k)).re = (chi (m + 3) k).re := by rw [← chi_conj]; simp
    have hn1 : normSq (1 - chi (m + 3) (-k)) = 2 - 2 * (chi (m + 3) k).re := by
      have hns := chi_normSq (N := m + 3) (-k)
      rw [Complex.normSq_apply] at hns
      rw [hre] at hns
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hre]
      linear_combination hns
    rw [hsplit, Complex.normSq_mul, hn1]
  have h2 : ∑ k : ZMod (m + 3), (2 - 2 * (chi (m + 3) k).re) *
        normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k))
      = ((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j - x (j + 1)) ^ 2 := by
    have h := parseval (N := m + 3) (fun j => ((x j - x (j + 1) : ℝ) : ℂ))
    rw [Finset.sum_congr rfl (fun k _ => (hterm k).symm)]
    simpa [← Complex.ofReal_sub, Complex.normSq_ofReal, sq] using h
  have h4 : ∀ k : ZMod (m + 3),
      (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
          normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k))
        ≤ (2 - 2 * (chi (m + 3) k).re) *
          normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [h3]; ring_nf; rfl
    · have hAk : 0 ≤ normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)) :=
        normSq_nonneg _
      have hcos : (chi (m + 3) k).re ≤ Real.cos (2 * Real.pi / (m + 3)) := by
        rw [chi_re]
        have hv1 : 1 ≤ k.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk)
        have hb := cos_two_pi_mul_le (m + 3) k.val hv1 k.val_lt
        push_cast at hb ⊢
        exact hb
      nlinarith
  have hchain : (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
      (((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j) ^ 2)
      ≤ ((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j - x (j + 1)) ^ 2 := by
    rw [← h1, ← h2, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => h4 k)
  rw [show (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
      (((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j) ^ 2)
      = ((m + 3 : ℕ) : ℝ) * ((2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
        ∑ j : ZMod (m + 3), (x j) ^ 2) from by ring] at hchain
  exact le_of_mul_le_mul_left hchain hNpos

/-- The eigenvector realizing the Fiedler value. -/
