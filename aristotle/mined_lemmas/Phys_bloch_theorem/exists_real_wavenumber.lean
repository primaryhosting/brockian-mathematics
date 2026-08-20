/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The translation operator by a lattice period `a`, acting on wave functions
`ψ : ℝ → ℂ` by `(T_a ψ)(x) = ψ (x + a)`. -/

theorem exists_real_wavenumber {c : ℂ} (hc : ‖c‖ = 1) {a : ℝ} (ha : a ≠ 0) :
    ∃ k : ℝ, c = Complex.exp (Complex.I * k * a) := by
  refine ⟨Complex.arg c / a, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc] at h
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hka : ((Complex.arg c / a : ℝ) : ℂ) * a = (Complex.arg c : ℂ) := by
    push_cast
    exact div_mul_cancel₀ _ ha'
  rw [mul_assoc, hka]
  conv_lhs => rw [← h]
  rw [mul_comm Complex.I]
  simp

/-- **Floquet/Bloch factorization.** A wave function satisfying the translation eigenvalue
relation `ψ (x + a) = e^{i k a} ψ (x)` is a Bloch wave: `ψ (x) = e^{i k x} u (x)` with `u`
periodic of period `a`. -/
