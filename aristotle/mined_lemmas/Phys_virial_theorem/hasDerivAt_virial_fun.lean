/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem hasDerivAt_virial_fun
    {psi dpsi ddpsi V dV : ℝ → ℝ} {E : ℝ}
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSch : ∀ x, -ddpsi x + V x * psi x = E * psi x) (x : ℝ) :
    HasDerivAt (fun y => y * (dpsi y ^ 2 + (E - V y) * psi y ^ 2))
      (dpsi x ^ 2 + (E - V x) * psi x ^ 2 - x * dV x * psi x ^ 2) x := by
  have hdd : ddpsi x = (V x - E) * psi x := by
    have := hSch x; linarith [this]
  have d1 : HasDerivAt (fun y => dpsi y ^ 2) (2 * dpsi x * ddpsi x) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hdpsi x).pow 2
  have d2 : HasDerivAt (fun y => psi y ^ 2) (2 * psi x * dpsi x) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hpsi x).pow 2
  have d3 : HasDerivAt (fun y => E - V y) (-dV x) x := by
    simpa using (hasDerivAt_const x E).sub (hV x)
  have d4 := d3.mul d2
  have d5 := d1.add d4
  have d6 := (hasDerivAt_id x).mul d5
  convert d6 using 1
  simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  rw [hdd]
  ring

/-- **Quantum virial theorem** (one dimension, units `ħ² / 2m = 1`).

Let `psi` be a stationary state of the Schrödinger operator `H = -d²/dx² + V` with energy
`E`, i.e. `-ψ'' + V ψ = E ψ`, and assume the bound-state conditions: the kinetic density
`ψ'²`, the potential density `V ψ²`, the density `ψ²` and the virial density `x V'(x) ψ²`
are all integrable, and the boundary terms `ψ ψ'` and `x (ψ'² + (E - V) ψ²)` vanish at
`±∞`.  Then
`2 ⟨T⟩ = ⟨x · V'(x)⟩`,
the one-dimensional form of `2⟨T⟩ = ⟨r · ∇V⟩`. -/
