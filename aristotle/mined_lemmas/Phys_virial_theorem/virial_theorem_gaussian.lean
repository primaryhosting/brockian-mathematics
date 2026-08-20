/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology

namespace Phys

/-- **Quantum virial theorem** (one spatial dimension, units `ħ = m = 1`).

Let `ψ : ℝ → ℝ` be a stationary state of the Schrödinger operator `H = -(1/2) d²/dx² + V`
with energy `E`, i.e. `-(1/2) ψ'' + V ψ = E ψ`, where `dψ`, `ddψ` are the first and second
derivatives of `ψ` and `dV` is the derivative of the potential `V`.

Boundedness of the state enters through two kinds of hypotheses, exactly as in the physics
derivation:

* *integrability*: the kinetic density `(ψ')²` and the virial density `x V'(x) ψ(x)²`
  are integrable over `ℝ`;
* *decay at infinity*: the boundary terms produced by the integrations by parts,
  namely `x (ψ')²`, `x V ψ²`, `x ψ²` and `ψ ψ'`, vanish at `±∞`.

The conclusion is `2⟨T⟩ = ⟨x V'(x)⟩`, where `⟨T⟩ = ∫ (1/2)(ψ')²` is the expectation value of
the kinetic energy and `⟨x V'⟩ = ∫ x V'(x) ψ(x)²` is the expectation value of the virial
`r · ∇V`, both taken in the state `ψ`. (For a normalized state `∫ ψ² = 1` these integrals are
literally the quantum-mechanical expectation values; normalization is not needed for the
identity, since both sides are homogeneous of degree two in `ψ`.)

The proof is a single integration by parts: the function
`Φ = x (ψ')² - 2 x V ψ² + 2 E x ψ² + ψ ψ'`
satisfies, thanks to the eigenvalue equation, `Φ' = 2((ψ')² - x V' ψ²)`, and `Φ → 0` at `±∞`.
-/

theorem virial_theorem_gaussian :
    2 * (∫ x, (1 / 2) * gaussState' x ^ 2) = ∫ x, x * x * gaussState x ^ 2 := by
  have hTfun : (fun x => gaussState' x ^ 2) = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) :=
    funext gauss_kinetic_density
  have hWfun : (fun x : ℝ => x * (fun y : ℝ => y) x * gaussState x ^ 2)
      = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := funext gauss_virial_density
  refine virial_theorem gaussState gaussState' gaussState'' hoPotential (fun x => x) (1 / 2)
    hasDerivAt_gaussState hasDerivAt_gaussState' (fun x => ?_) (fun x => ?_)
    (hTfun ▸ gauss_integrable) (hWfun ▸ gauss_integrable) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the potential is differentiable
    simpa [hoPotential] using (hasDerivAt_pow 2 x).div_const 2
  · -- the Schrödinger equation
    simp only [gaussState, gaussState'', hoPotential]
    ring
  · -- boundary term `x (ψ')²` at `-∞`
    exact (gauss_tendsto_atBot 3).congr fun x => by rw [gauss_kinetic_density]; ring
  · exact (gauss_tendsto_atTop 3).congr fun x => by rw [gauss_kinetic_density]; ring
  · -- boundary term `x V ψ²` at `-∞`
    have h : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * (x ^ 3 * Real.exp (-x ^ 2))) atBot (𝓝 0) := by
      simpa using (gauss_tendsto_atBot 3).const_mul (1 / 2 : ℝ)
    refine h.congr fun x => ?_
    simp only [gaussState, hoPotential, gauss_sq]; ring
  · have h : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * (x ^ 3 * Real.exp (-x ^ 2))) atTop (𝓝 0) := by
      simpa using (gauss_tendsto_atTop 3).const_mul (1 / 2 : ℝ)
    refine h.congr fun x => ?_
    simp only [gaussState, hoPotential, gauss_sq]; ring
  · -- boundary term `x ψ²` at `-∞`
    refine (gauss_tendsto_atBot 1).congr fun x => ?_
    simp only [gaussState, gauss_sq]; ring
  · refine (gauss_tendsto_atTop 1).congr fun x => ?_
    simp only [gaussState, gauss_sq]; ring
  · -- boundary term `ψ ψ'` at `-∞`
    have h : Tendsto (fun x : ℝ => -(x ^ 1 * Real.exp (-x ^ 2))) atBot (𝓝 0) := by
      simpa using (gauss_tendsto_atBot 1).neg
    exact h.congr fun x => (gauss_cross_density x).symm
  · have h : Tendsto (fun x : ℝ => -(x ^ 1 * Real.exp (-x ^ 2))) atTop (𝓝 0) := by
      simpa using (gauss_tendsto_atTop 1).neg
    exact h.congr fun x => (gauss_cross_density x).symm

/-- The kinetic energy of the Gaussian ground state is strictly positive, so
`virial_theorem_gaussian` is not a triviality about vanishing integrals. -/
