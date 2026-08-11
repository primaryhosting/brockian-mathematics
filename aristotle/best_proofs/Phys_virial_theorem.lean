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
noncomputable def gaussState : ℝ → ℝ := fun x => Real.exp (-x ^ 2 / 2)

/-- The derivative of `gaussState`. -/
noncomputable def gaussState' : ℝ → ℝ := fun x => -x * Real.exp (-x ^ 2 / 2)

/-- The second derivative of `gaussState`. -/
noncomputable def gaussState'' : ℝ → ℝ := fun x => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)

/-- The harmonic oscillator potential `V(x) = x²/2`. -/
noncomputable def hoPotential : ℝ → ℝ := fun x => x ^ 2 / 2

theorem gauss_sq (x : ℝ) : Real.exp (-x ^ 2 / 2) ^ 2 = Real.exp (-x ^ 2) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem hasDerivAt_gaussExponent (x : ℝ) : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
  have h := (hasDerivAt_pow 2 x).neg.div_const 2
  convert h using 1
  push_cast; ring

theorem hasDerivAt_gaussState (x : ℝ) : HasDerivAt gaussState (gaussState' x) x := by
  simpa [gaussState, gaussState', mul_comm] using (hasDerivAt_gaussExponent x).exp

theorem hasDerivAt_gaussState' (x : ℝ) : HasDerivAt gaussState' (gaussState'' x) x := by
  have h := (hasDerivAt_neg x).mul (hasDerivAt_gaussState x)
  simp only [gaussState, gaussState', gaussState''] at h ⊢
  convert h using 1
  ring

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

theorem gauss_tendsto_atBot (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := gauss_tendsto_atTop n
  rw [tendsto_zero_iff_norm_tendsto_zero] at h
  exact (h.comp tendsto_neg_atBot_atTop).congr (by intro x; simp [Function.comp])

theorem gauss_integrable : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)
  simpa [Real.rpow_natCast] using h

theorem gauss_kinetic_density (x : ℝ) : gaussState' x ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := by
  have h : gaussState' x ^ 2 = x ^ 2 * Real.exp (-x ^ 2 / 2) ^ 2 := by
    simp only [gaussState']; ring
  rw [h, gauss_sq]

theorem gauss_virial_density (x : ℝ) : x * x * gaussState x ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := by
  have h : x * x * gaussState x ^ 2 = x ^ 2 * Real.exp (-x ^ 2 / 2) ^ 2 := by
    simp only [gaussState]; ring
  rw [h, gauss_sq]

theorem gauss_cross_density (x : ℝ) :
    gaussState x * gaussState' x = -(x ^ 1 * Real.exp (-x ^ 2)) := by
  have h : gaussState x * gaussState' x = -(x ^ 1 * Real.exp (-x ^ 2 / 2) ^ 2) := by
    simp only [gaussState, gaussState']; ring
  rw [h, gauss_sq]

/-- The virial theorem applies to the harmonic oscillator ground state: all of its hypotheses
are satisfiable, so the statement is not vacuous. -/
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

