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

theorem bloch_factorization {a k : ℝ} {ψ : ℝ → ℂ}
    (hψ : ∀ x, ψ (x + a) = Complex.exp (Complex.I * k * a) * ψ x) :
    ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧ ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x := by
  refine ⟨fun x => Complex.exp (-(Complex.I * k * x)) * ψ x, fun x => ?_, fun x => ?_⟩
  · dsimp only
    rw [hψ x, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  · dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**

Let `H` be a Hamiltonian on wave functions `ψ : ℝ → ℂ` which commutes with translation by the
lattice period `a ≠ 0` (for instance a kinetic term plus a periodic potential, see
`Phys.commutesWithTranslation_kinetic_add_periodic_potential`).  Let `ψ` be an eigenstate of `H`
with eigenvalue `E`, spanning its eigenspace, whose probability density `‖ψ‖²` is unchanged by
the lattice translation.

Then `ψ` is a *Bloch wave*: there is a real wavenumber `k` (the crystal momentum) and a
lattice-periodic function `u` such that

  `ψ (x) = e^{i k x} · u (x)`,  `u (x + a) = u (x)`,

and moreover `ψ` satisfies the Bloch boundary condition `ψ (x + a) = e^{i k a} ψ (x)`. -/
