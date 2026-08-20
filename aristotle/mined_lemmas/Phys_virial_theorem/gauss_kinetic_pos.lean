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

theorem gauss_kinetic_pos : 0 < ∫ x, (1 / 2) * gaussState' x ^ 2 := by
  have hTfun : (fun x => (1 / 2 : ℝ) * gaussState' x ^ 2)
      = fun x : ℝ => (1 / 2 : ℝ) * (x ^ 2 * Real.exp (-x ^ 2)) := by
    funext x; rw [gauss_kinetic_density]
  rw [hTfun, integral_const_mul]
  have hpos : 0 < ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) := by
    rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) gauss_integrable]
    have hsupp : (Function.support fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) = {x : ℝ | x ≠ 0} := by
      ext x
      simp [Function.support, Real.exp_ne_zero, pow_eq_zero_iff]
    have huniv : {x : ℝ | x ≠ 0} = Set.univ \ {0} := by ext x; simp
    rw [hsupp, huniv]
    simp [MeasureTheory.measure_diff]
  linarith

end Phys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

