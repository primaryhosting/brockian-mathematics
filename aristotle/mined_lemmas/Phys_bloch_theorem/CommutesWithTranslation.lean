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

def CommutesWithTranslation (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ ψ : ℝ → ℂ, H (translate a ψ) = translate a (H ψ)

/-- A Hamiltonian of the form `H = T + V` (a translation-invariant kinetic term `T`
plus multiplication by a potential `V` with period `a`) commutes with translation by `a`.
This justifies the hypothesis `CommutesWithTranslation` in Bloch's theorem. -/
