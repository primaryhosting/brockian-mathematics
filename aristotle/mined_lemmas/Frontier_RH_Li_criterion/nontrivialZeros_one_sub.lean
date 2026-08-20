/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem nontrivialZeros_one_sub {s : ℂ} (hs : s ∈ nontrivialZeros) : 1 - s ∈ nontrivialZeros := by
  obtain ⟨hz, htriv, hone⟩ := hs
  have hs0 : s ≠ 0 := ne_zero_of_mem_nontrivialZeros ⟨hz, htriv, hone⟩
  have hGne : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hs0 (by simpa using hn)
    · refine htriv ⟨n - 1, ?_⟩
      have hone' : ((n : ℂ) - 1 + 1) = n := by ring
      have hcast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        have h1n : (1 : ℕ) ≤ n := hpos
        push_cast [Nat.cast_sub h1n]
        ring
      rw [hn, hcast, hone']
      ring
  have hLam : completedRiemannZeta s = 0 := by
    have h := riemannZeta_def_of_ne_zero hs0
    rw [hz] at h
    rcases div_eq_zero_iff.mp h.symm with h1 | h1
    · exact h1
    · exact absurd h1 hGne
  have hLam2 : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]; exact hLam
  have h1s0 : (1 : ℂ) - s ≠ 0 := fun h => hone (by linear_combination -h)
  refine ⟨by rw [riemannZeta_def_of_ne_zero h1s0, hLam2, zero_div], ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hs' : s = 2 * n + 3 := by linear_combination -hn
    have hre : 1 < s.re := by
      rw [hs']
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact riemannZeta_ne_zero_of_one_lt_re hre hz
  · exact fun h => hs0 (by linear_combination -h)

/-- For `s ≠ 0`, the point `1 - 1/s` lies in the closed unit disc iff `Re s ≥ 1/2`. -/
