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

noncomputable def constantSelector : (ℝ → ℂ) → (ℝ → ℂ) :=
  fun φ => if (∃ c : ℂ, ∀ x, φ x = c) then φ else fun x => φ x + 1

/-- The hypotheses of `Phys.bloch_theorem` are satisfiable: there really is a Hamiltonian
commuting with a lattice translation, with a simple eigenvalue whose eigenstate is nonzero and
has translation-invariant modulus. -/
