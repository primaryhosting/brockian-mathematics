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

theorem virial_theorem
    (ψ dψ ddψ V dV : ℝ → ℝ) (E : ℝ)
    (hψ : ∀ x, HasDerivAt ψ (dψ x) x)
    (hdψ : ∀ x, HasDerivAt dψ (ddψ x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSch : ∀ x, -(1 / 2) * ddψ x + V x * ψ x = E * ψ x)
    (hT : Integrable (fun x => dψ x ^ 2))
    (hW : Integrable (fun x => x * dV x * ψ x ^ 2))
    (hb1 : Tendsto (fun x => x * dψ x ^ 2) atBot (𝓝 0))
    (ht1 : Tendsto (fun x => x * dψ x ^ 2) atTop (𝓝 0))
    (hb2 : Tendsto (fun x => x * V x * ψ x ^ 2) atBot (𝓝 0))
    (ht2 : Tendsto (fun x => x * V x * ψ x ^ 2) atTop (𝓝 0))
    (hb3 : Tendsto (fun x => x * ψ x ^ 2) atBot (𝓝 0))
    (ht3 : Tendsto (fun x => x * ψ x ^ 2) atTop (𝓝 0))
    (hb4 : Tendsto (fun x => ψ x * dψ x) atBot (𝓝 0))
    (ht4 : Tendsto (fun x => ψ x * dψ x) atTop (𝓝 0)) :
    2 * (∫ x, (1 / 2) * dψ x ^ 2) = ∫ x, x * dV x * ψ x ^ 2 := by
  set Φ : ℝ → ℝ :=
    fun y => y * dψ y ^ 2 - 2 * (y * V y * ψ y ^ 2) + 2 * E * (y * ψ y ^ 2) + ψ y * dψ y with hΦ
  -- The derivative of `Φ`.
  have hderiv : ∀ x, HasDerivAt Φ (2 * (dψ x ^ 2 - x * dV x * ψ x ^ 2)) x := by
    intro x
    have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have hsq : HasDerivAt (fun y => ψ y ^ 2) ((2 : ℕ) * ψ x ^ 1 * dψ x) x := (hψ x).pow 2
    have hdsq : HasDerivAt (fun y => dψ y ^ 2) ((2 : ℕ) * dψ x ^ 1 * ddψ x) x := (hdψ x).pow 2
    have hA : HasDerivAt (fun y => y * dψ y ^ 2)
        (1 * dψ x ^ 2 + x * ((2 : ℕ) * dψ x ^ 1 * ddψ x)) x := hid.mul hdsq
    have hB : HasDerivAt (fun y => y * V y * ψ y ^ 2)
        ((1 * V x + x * dV x) * ψ x ^ 2 + x * V x * ((2 : ℕ) * ψ x ^ 1 * dψ x)) x :=
      (hid.mul (hV x)).mul hsq
    have hC : HasDerivAt (fun y => y * ψ y ^ 2)
        (1 * ψ x ^ 2 + x * ((2 : ℕ) * ψ x ^ 1 * dψ x)) x := hid.mul hsq
    have hD : HasDerivAt (fun y => ψ y * dψ y) (dψ x * dψ x + ψ x * ddψ x) x :=
      (hψ x).mul (hdψ x)
    have := ((hA.sub (hB.const_mul 2)).add (hC.const_mul (2 * E))).add hD
    have heq : ddψ x = 2 * (V x - E) * ψ x := by
      have := hSch x; linarith [this]
    convert this using 1
    push_cast
    linear_combination (-(2 * x * dψ x + ψ x)) * heq
  have hint : Integrable (fun x => 2 * (dψ x ^ 2 - x * dV x * ψ x ^ 2)) :=
    (hT.sub hW).const_mul 2
  have hΦbot : Tendsto Φ atBot (𝓝 0) := by
    have := ((hb1.sub (hb2.const_mul 2)).add (hb3.const_mul (2 * E))).add hb4
    simpa [hΦ] using this
  have hΦtop : Tendsto Φ atTop (𝓝 0) := by
    have := ((ht1.sub (ht2.const_mul 2)).add (ht3.const_mul (2 * E))).add ht4
    simpa [hΦ] using this
  have hzero : ∫ x, 2 * (dψ x ^ 2 - x * dV x * ψ x ^ 2) = 0 := by
    have := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hint hΦbot hΦtop
    simpa using this
  rw [integral_const_mul, integral_sub hT hW] at hzero
  rw [integral_const_mul]
  linarith [hzero]

/-!
## Non-vacuity: the harmonic oscillator ground state

All hypotheses of `Phys.virial_theorem` are satisfied by the ground state
`ψ(x) = exp(-x²/2)` of the harmonic oscillator `V(x) = x²/2`, with energy `E = 1/2`,
and the corresponding kinetic energy is strictly positive.
-/

/-- The Gaussian ground state `exp(-x²/2)` of the harmonic oscillator. -/
