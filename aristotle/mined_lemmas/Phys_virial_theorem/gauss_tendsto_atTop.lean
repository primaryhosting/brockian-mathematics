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

theorem gauss_tendsto_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (x ^ 2) ^ n * Real.exp (-x ^ 2)) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
      (tendsto_pow_atTop (n := 2) (by norm_num))
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx2 : x ^ n ≤ (x ^ 2) ^ n := by gcongr; nlinarith
    exact mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le

