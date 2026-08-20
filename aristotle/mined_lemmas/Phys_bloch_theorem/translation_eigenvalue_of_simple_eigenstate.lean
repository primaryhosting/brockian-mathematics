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

theorem translation_eigenvalue_of_simple_eigenstate
    {a : ℝ} {H : (ℝ → ℂ) → (ℝ → ℂ)} {E : ℂ} {ψ : ℝ → ℂ}
    (hH : CommutesWithTranslation a H)
    (hEig : H ψ = fun x => E * ψ x)
    (hsimple : ∀ φ : ℝ → ℂ, (H φ = fun x => E * φ x) → ∃ c : ℂ, ∀ x, φ x = c * ψ x) :
    ∃ c : ℂ, ∀ x, ψ (x + a) = c * ψ x := by
  have hφ : H (translate a ψ) = fun x => E * translate a ψ x := by
    rw [hH ψ, hEig]
    rfl
  obtain ⟨c, hc⟩ := hsimple _ hφ
  exact ⟨c, hc⟩

/-- A complex number of modulus one is `exp (I * k * a)` for a real `k` (given `a ≠ 0`). -/
