/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Phys

/-- Translation of a wave function by the lattice constant `a`: `(transl a f) x = f (x + a)`. -/

lemma norm_le_one_of_bounded {A : ℝ} {c : ℂ} {f : ℝ → ℂ} {M : ℝ}
    (h : ∀ x, f (x + A) = c * f x) (hM : ∀ x, ‖f x‖ ≤ M) {x₀ : ℝ} (hx₀ : f x₀ ≠ 0) :
    ‖c‖ ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hpos : 0 < ‖f x₀‖ := norm_pos_iff.mpr hx₀
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖f x₀‖) hc
  have key : ‖f (x₀ + n * A)‖ = ‖c‖ ^ n * ‖f x₀‖ := by
    rw [shift_pow h n x₀, norm_mul, norm_pow]
  have h1 : M < ‖c‖ ^ n * ‖f x₀‖ := by
    rw [div_lt_iff₀ hpos] at hn
    exact hn
  have h2 : ‖f (x₀ + n * A)‖ ≤ M := hM _
  rw [key] at h2
  linarith

end Helpers

/-- **Bloch's theorem.**  Let `H` be a Hamiltonian on wave functions `ℝ → ℂ` that is periodic
with lattice constant `a > 0` (i.e. commutes with translation by `a`).  Let `ψ` be a bounded,
nonzero eigenstate of `H` with eigenvalue `E`, and assume the eigenvalue `E` is nondegenerate
(every eigenstate with eigenvalue `E` is a scalar multiple of `ψ`).

Then there is a crystal momentum `k : ℝ` and a lattice-periodic function `u` such that
`ψ x = e^{i k x} u x`, i.e. `ψ` is a Bloch wave. -/
