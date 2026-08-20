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
-/

set_option autoImplicit false

namespace Phys

open Complex

/-- Translation of a wavefunction by `a`: `(translate a ψ) x = ψ (x + a)`. -/

theorem norm_translation_eigenvalue_eq_one {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {M : ℝ} {x₀ : ℝ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x) (hM : ∀ x : ℝ, ‖ψ x‖ ≤ M) (hx₀ : ψ x₀ ≠ 0) :
    ‖lam‖ = 1 := by
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x₀)
  have hnorm : ∀ (n : ℕ) (x : ℝ), ‖ψ (x + n * a)‖ = ‖lam‖ ^ n * ‖ψ x‖ := by
    intro n x
    rw [translate_iterate hT n x, norm_mul, norm_pow]
  have hle : ‖lam‖ ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖ψ x₀‖) h
    rw [div_lt_iff₀ hpos] at hn
    have h2 := hM (x₀ + n * a)
    rw [hnorm n x₀] at h2
    linarith
  have hge : 1 ≤ ‖lam‖ := by
    by_contra h
    push_neg at h
    have hMpos : 0 < M + 1 := by linarith
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hpos hMpos) h
    have key : ‖ψ x₀‖ = ‖lam‖ ^ n * ‖ψ (x₀ - n * a)‖ := by
      have := hnorm n (x₀ - n * a)
      simpa using this
    have hb : ‖ψ (x₀ - n * a)‖ ≤ M := hM _
    have hpow : (0:ℝ) ≤ ‖lam‖ ^ n := pow_nonneg (norm_nonneg lam) n
    rw [lt_div_iff₀ hMpos] at hn
    nlinarith
  exact le_antisymm hle hge

/--
**Bloch's theorem.**  Let `a ≠ 0` be the lattice period and let `ψ` be a simultaneous
eigenstate of a periodic Hamiltonian and of the translation operator `T_a`, with eigenvalue
`lam` of unit modulus (as is forced by unitarity of `T_a`).  Then there is a crystal momentum
`k : ℝ` and an `a`-periodic function `u` such that

  `ψ x = e^{i k x} * u x`,   `u (x + a) = u x`,   `lam = e^{i k a}`,

i.e. `ψ` is a Bloch wave.

The key Mathlib ingredient is `Complex.norm_eq_one_iff`, which writes a unit-modulus
complex number as `exp (θ * I)`.
-/
