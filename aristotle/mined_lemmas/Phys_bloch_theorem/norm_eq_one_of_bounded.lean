/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Eigenstates of a periodic Hamiltonian are Bloch waves `e^{ikx} u_k(x)`.

The development is organised as follows.

* `Phys.schrodinger` : the one-dimensional Schrödinger operator `ψ ↦ -ψ'' + V ψ`.
* `Phys.IsEigenstate` : `ψ` solves `-ψ'' + V ψ = E ψ`.
* `Phys.isEigenstate_translate` : the Hamiltonian commutes with translation by a period of `V`.
* `Phys.norm_eq_one_of_bounded` : a bounded nonzero `ψ` with `ψ (x + a) = c ψ (x)` has `‖c‖ = 1`.
* `Phys.bloch_theorem` : the main result.
* `Phys.bloch_theorem_of_translation_eigenvalue` : the same conclusion starting directly from
  the translation-eigenvalue property.
* `Phys.bloch_hypotheses_satisfiable` : the hypotheses of `bloch_theorem` are consistent
  (they are met by the constant potential with the constant eigenstate).
-/

namespace Phys

open Complex

/-- The one-dimensional Schrödinger operator with potential `V` (units `ℏ²/2m = 1`),
acting on functions `ψ : ℝ → ℂ`. -/

theorem norm_eq_one_of_bounded {a : ℝ} {c : ℂ} {psi : ℝ → ℂ}
    (hc : ∀ x, psi (x + a) = c * psi x)
    (hne : ∃ x₀, psi x₀ ≠ 0) (hbdd : ∃ C, ∀ x, ‖psi x‖ ≤ C) :
    ‖c‖ = 1 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨C, hC⟩ := hbdd
  set M := ‖psi x₀‖ with hM
  have hM0 : 0 < M := norm_pos_iff.mpr hx₀
  have hMC : M ≤ C := hC x₀
  have hC0 : 0 < C := lt_of_lt_of_le hM0 hMC
  have key : ∀ n : ℕ, ‖c‖ ^ n * M ≤ C := by
    intro n
    have h := iterate_translate hc n x₀
    have hnorm : ‖c‖ ^ n * M = ‖psi (x₀ + n * a)‖ := by
      rw [h, norm_mul, norm_pow]
    rw [hnorm]
    exact hC _
  have key2 : ∀ n : ℕ, M ≤ ‖c‖ ^ n * C := by
    intro n
    have h := iterate_translate hc n (x₀ - n * a)
    have hx : x₀ - (n : ℝ) * a + n * a = x₀ := by ring
    rw [hx] at h
    have hnorm : M = ‖c‖ ^ n * ‖psi (x₀ - n * a)‖ := by
      rw [hM, h, norm_mul, norm_pow]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hle : ‖c‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / M) hgt
    have h2 : C < ‖c‖ ^ n * M := by
      rw [div_lt_iff₀ hM0] at hn
      linarith
    linarith [key n]
  have hge : 1 ≤ ‖c‖ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < M / C by positivity) hlt
    have h2 : ‖c‖ ^ n * C < M := by
      rw [lt_div_iff₀ hC0] at hn
      linarith
    linarith [key2 n]
  linarith

/-- **Bloch's theorem, translation-eigenvalue form.**  A bounded nonzero function which is an
eigenvector of the translation by `a > 0` is a Bloch wave: `ψ x = e^{i k x} u x` with `u`
`a`-periodic. -/
