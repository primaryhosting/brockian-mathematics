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

theorem commutesWithTranslation_kinetic_add_periodic_potential
    {a : ℝ} (T : (ℝ → ℂ) → (ℝ → ℂ)) (V : ℝ → ℂ)
    (hT : CommutesWithTranslation a T) (hV : ∀ x, V (x + a) = V x) :
    CommutesWithTranslation a (fun ψ => fun x => T ψ x + V x * ψ x) := by
  intro ψ
  funext x
  have hTψ : T (translate a ψ) x = T ψ (x + a) := by
    rw [hT ψ]; rfl
  simp only [translate, hTψ, hV x]

/-- **Simultaneous diagonalization step.** If the Hamiltonian `H` commutes with translation
by `a` and `ψ` spans a (simple) eigenspace of `H` for the eigenvalue `E`, then `ψ` is also an
eigenfunction of the translation operator: `ψ (x + a) = c * ψ x` for some constant `c`. -/
