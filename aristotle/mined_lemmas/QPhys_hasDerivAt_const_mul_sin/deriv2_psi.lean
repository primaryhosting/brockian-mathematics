/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

lemma deriv2_psi (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (psi L n)) x = -((n * Real.pi / L) ^ 2) * psi L n x := by
  rw [deriv_psi, psi_eq]
  have := (hasDerivAt_const_mul_cos (Real.sqrt (2 / L) * (n * Real.pi / L))
      (n * Real.pi / L) x).deriv
  rw [this]
  ring

/-- Quantization: a positive wave number `k` with a node at `x = L` is of the form `nπ/L`
with `n ≥ 1`. -/
