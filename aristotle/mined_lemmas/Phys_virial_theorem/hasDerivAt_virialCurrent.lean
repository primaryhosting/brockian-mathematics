/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology

namespace Phys

/-- The auxiliary "virial current"
`F x = x * ψ' x ^ 2 - x * (V x - E) * ψ x ^ 2 + ψ x * ψ' x`,
whose derivative is exactly `2 * ψ' x ^ 2 - x * V' x * ψ x ^ 2` for a solution of the
stationary Schrödinger equation. -/

theorem hasDerivAt_virialCurrent
    (psi psi1 psi2 V V1 : ℝ → ℝ) (E : ℝ)
    (hpsi : ∀ x, HasDerivAt psi (psi1 x) x)
    (hpsi1 : ∀ x, HasDerivAt psi1 (psi2 x) x)
    (hV : ∀ x, HasDerivAt V (V1 x) x)
    (hSch : ∀ x, -psi2 x + V x * psi x = E * psi x) (x : ℝ) :
    HasDerivAt (virialCurrent psi psi1 V E)
      (2 * psi1 x ^ 2 - x * V1 x * psi x ^ 2) x := by
  have hpsi2eq : psi2 x = (V x - E) * psi x := by
    linarith [hSch x]
  have h1 : HasDerivAt (fun y => y * psi1 y ^ 2)
      (1 * psi1 x ^ 2 + x * (2 * psi1 x * psi2 x)) x := by
    have hsq : HasDerivAt (fun y => psi1 y ^ 2) (2 * psi1 x * psi2 x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hpsi1 x).pow 2
    exact (hasDerivAt_id x).mul hsq
  have h2 : HasDerivAt (fun y => y * (V y - E) * psi y ^ 2)
      ((1 * (V x - E) + x * V1 x) * psi x ^ 2
        + x * (V x - E) * (2 * psi x * psi1 x)) x := by
    have hVE : HasDerivAt (fun y => V y - E) (V1 x) x := (hV x).sub_const E
    have ha : HasDerivAt (fun y => y * (V y - E)) (1 * (V x - E) + x * V1 x) x :=
      (hasDerivAt_id x).mul hVE
    have hsq : HasDerivAt (fun y => psi y ^ 2) (2 * psi x * psi1 x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hpsi x).pow 2
    exact ha.mul hsq
  have h3 : HasDerivAt (fun y => psi y * psi1 y) (psi1 x * psi1 x + psi x * psi2 x) x :=
    (hpsi x).mul (hpsi1 x)
  have := (h1.sub h2).add h3
  convert this using 1
  rw [hpsi2eq]
  ring

/-- **Quantum virial theorem** (one dimension, units in which the Hamiltonian is
`H = -d²/dx² + V`).

Let `psi` be a bound stationary state: a twice-differentiable real wave function with
`psi1 = psi'`, `psi2 = psi''`, satisfying the time-independent Schrödinger equation
`-psi'' + V psi = E psi` for a differentiable potential `V` with derivative `V1 = V'`.
Assume the kinetic and virial densities are integrable, and that the boundary term
`virialCurrent` (which involves `x psi'^2`, `x (V - E) psi^2` and `psi psi'`) vanishes at
`±∞` — this is what "bound state" provides.

Then `2⟨T⟩ = ⟨x ∂V/∂x⟩`, where `⟨T⟩ = ∫ psi'^2` (the expectation of `-d²/dx²`) and
`⟨x V'⟩ = ∫ x V' psi^2`
(no normalization of `psi` is needed for this identity). -/
