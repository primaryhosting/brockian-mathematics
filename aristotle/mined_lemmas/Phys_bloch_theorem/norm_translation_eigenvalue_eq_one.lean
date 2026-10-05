/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Complex

/-- `f` has period `a`. -/

theorem norm_translation_eigenvalue_eq_one {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {C : ℝ}
    (h : ∀ x, ψ (x + a) = lam * ψ x) (hbdd : ∀ x, ‖ψ x‖ ≤ C)
    {x₀ : ℝ} (hx₀ : ψ x₀ ≠ 0) : ‖lam‖ = 1 := by
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hle : ‖lam‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖ψ x₀‖) hgt
    have hkey : ‖lam‖ ^ n * ‖ψ x₀‖ ≤ C := by
      have := hbdd (x₀ + n * a)
      rwa [translate_pow h n x₀, norm_mul, norm_pow] at this
    have : C / ‖ψ x₀‖ < ‖lam‖ ^ n := hn
    rw [div_lt_iff₀ hpos] at this
    linarith [hkey, this]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbdd x₀)
  have hge : 1 ≤ ‖lam‖ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ‖ψ x₀‖ / (C + 1)) (y := ‖lam‖)
      (div_pos hpos (by linarith)) hlt
    have hkey : ‖ψ x₀‖ ≤ ‖lam‖ ^ n * C := by
      have h1 := translate_pow_neg h n x₀
      have h2 : ‖ψ x₀‖ = ‖lam‖ ^ n * ‖ψ (x₀ - n * a)‖ := by
        rw [h1, norm_mul, norm_pow]
      rw [h2]
      have := hbdd (x₀ - n * a)
      nlinarith [pow_nonneg (norm_nonneg lam) n, norm_nonneg (ψ (x₀ - (n:ℝ) * a))]
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < C + 1)] at hn
    nlinarith [pow_nonneg (norm_nonneg lam) n]
  linarith

/-- **Bloch's theorem.**  Let `V` be a potential periodic with period `a ≠ 0` and let `ψ`
be a bounded, nonzero eigenstate of the Hamiltonian `H = -d²/dx² + V` with energy `E`
whose eigenspace is nondegenerate (any eigenstate with the same energy is a multiple of
`ψ`).  Then `ψ` is a Bloch wave: `ψ x = e^{i k x} u x` with `u` periodic of period `a`. -/
