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

/-- The translation operator by `a` acting on wave functions. -/

theorem translate_eigenvalue_norm_eq_one (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ) (M : ℝ)
    (hbdd : ∀ x, ‖ψ x‖ ≤ M) (x₀ : ℝ) (hx₀ : ψ x₀ ≠ 0)
    (hψ : ∀ x, translate a ψ x = c * ψ x) : ‖c‖ = 1 := by
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hM : 0 < M := lt_of_lt_of_le hpos (hbdd x₀)
  have key : ∀ n : ℕ, ‖c‖ ^ n * ‖ψ x₀‖ ≤ M := by
    intro n
    have := translate_iterate a ψ c hψ x₀ n
    have h2 : ‖ψ (x₀ + n * a)‖ = ‖c‖ ^ n * ‖ψ x₀‖ := by
      rw [this]; simp
    rw [← h2]
    exact hbdd _
  have hle : ‖c‖ ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖ψ x₀‖) h
    have := key n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hge : 1 ≤ ‖c‖ := by
    by_contra h
    push_neg at h
    -- going backwards along the lattice, `ψ` would blow up
    have back : ∀ n : ℕ, ‖ψ x₀‖ ≤ ‖c‖ ^ n * M := by
      intro n
      have hstep := translate_iterate a ψ c hψ (x₀ - n * a) n
      have hx : x₀ - n * a + n * a = x₀ := by ring
      rw [hx] at hstep
      have : ‖ψ x₀‖ = ‖c‖ ^ n * ‖ψ (x₀ - n * a)‖ := by
        rw [hstep]; simp
      rw [this]
      have hc0 : (0 : ℝ) ≤ ‖c‖ ^ n := by positivity
      exact mul_le_mul_of_nonneg_left (hbdd _) hc0
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ‖ψ x₀‖ / M) (y := ‖c‖) (by positivity) h
    have := back n
    rw [lt_div_iff₀ hM] at hn
    linarith
  linarith

/-- **Bloch's theorem.**  If a wave function `ψ` is an eigenfunction of the translation
operator by the lattice constant `a` (which happens for eigenstates of a Hamiltonian with an
`a`-periodic potential, see `Phys.hamiltonian_comm_translate`), with an eigenvalue `c` of unit
modulus, then `ψ` is a Bloch wave: there are a crystal momentum `k : ℝ` and an `a`-periodic
function `u` with `ψ x = e ^ (i k x) * u x` for all `x`. -/
