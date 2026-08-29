/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Filter Topology
open RealInnerProductSpace

namespace Phys

section Virial

/-!
We work with a one–dimensional quantum system on the line.

* `u : ℝ → ℂ` is the wave function of a bound stationary state, `u'` its derivative and
  `u''` its second derivative.
* `V : ℝ → ℝ` is the potential and `V'` its derivative (so `x * V' x` is `r · ∇V`).
* `c = ℏ² / (2m) ` is the kinetic coefficient, so that the Hamiltonian is
  `H ψ = -c ψ'' + V ψ` and the stationary Schrödinger equation reads `H u = E u`.

The kinetic energy expectation value is `⟨T⟩ = ∫ ⟪u x, (-c) * u'' x⟫` (real inner product on
`ℂ`, i.e. the real part of the usual Hermitian pairing), and the virial expectation value is
`⟨r · ∇V⟩ = ∫ x * V' x * ‖u x‖²`.
-/

variable {c E : ℝ} {u u' u'' : ℝ → ℂ} {V V' : ℝ → ℝ}

/-- The Schrödinger equation `-c u'' + V u = E u`, rewritten as `c • u'' = (V - E) • u`. -/
private lemma smul_second_deriv
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x) (x : ℝ) :
    c • u'' x = (V x - E) • u x := by
  have h : (c : ℂ) * u'' x = ((V x - E : ℝ) : ℂ) * u x := by
    push_cast
    linear_combination -(hSch x)
  rw [Complex.real_smul, Complex.real_smul]
  exact h

/-- `c ⟪u, u''⟫ = (V - E) ‖u‖²`. -/
private lemma inner_u_u''
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x) (x : ℝ) :
    c * ⟪u x, u'' x⟫ = (V x - E) * ‖u x‖ ^ 2 := by
  have h := smul_second_deriv hSch x
  calc c * ⟪u x, u'' x⟫ = ⟪u x, c • u'' x⟫ := (real_inner_smul_right _ _ _).symm
    _ = ⟪u x, (V x - E) • u x⟫ := by rw [h]
    _ = (V x - E) * ⟪u x, u x⟫ := real_inner_smul_right _ _ _
    _ = (V x - E) * ‖u x‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]

/-- `c ⟪u', u''⟫ = (V - E) ⟪u, u'⟫`. -/
private lemma inner_u'_u''
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x) (x : ℝ) :
    c * ⟪u' x, u'' x⟫ = (V x - E) * ⟪u x, u' x⟫ := by
  have h := smul_second_deriv hSch x
  calc c * ⟪u' x, u'' x⟫ = ⟪u' x, c • u'' x⟫ := (real_inner_smul_right _ _ _).symm
    _ = ⟪u' x, (V x - E) • u x⟫ := by rw [h]
    _ = (V x - E) * ⟪u' x, u x⟫ := real_inner_smul_right _ _ _
    _ = (V x - E) * ⟪u x, u' x⟫ := by rw [real_inner_comm]

/-- Derivative of the probability density `‖u‖²`. -/
private lemma hasDerivAt_normSq (hu : ∀ x, HasDerivAt u (u' x) x) (x : ℝ) :
    HasDerivAt (fun t => ‖u t‖ ^ 2) (2 * ⟪u x, u' x⟫) x := by
  have h := (hu x).inner ℝ (hu x)
  simpa [real_inner_self_eq_norm_sq, real_inner_comm, two_mul] using h

/-- Derivative of the kinetic density `‖u'‖²`. -/
private lemma hasDerivAt_normSq_deriv (hu' : ∀ x, HasDerivAt u' (u'' x) x) (x : ℝ) :
    HasDerivAt (fun t => ‖u' t‖ ^ 2) (2 * ⟪u' x, u'' x⟫) x := by
  have h := (hu' x).inner ℝ (hu' x)
  simpa [real_inner_self_eq_norm_sq, real_inner_comm, two_mul] using h

/-- Derivative of the current-type quantity `⟪u, u'⟫`. -/
private lemma hasDerivAt_inner_u_u'
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x) (x : ℝ) :
    HasDerivAt (fun t => (⟪u t, u' t⟫ : ℝ)) (⟪u x, u'' x⟫ + ‖u' x‖ ^ 2) x := by
  have h := (hu x).inner ℝ (hu' x)
  simpa [real_inner_self_eq_norm_sq] using h

/-- The auxiliary function whose derivative is the virial density. -/
private noncomputable def virialAux (c E : ℝ) (u u' : ℝ → ℂ) (V : ℝ → ℝ) : ℝ → ℝ :=
  fun t => t * (c * ‖u' t‖ ^ 2 - (V t - E) * ‖u t‖ ^ 2) + c * ⟪u t, u' t⟫

/-- Key pointwise identity: the derivative of the auxiliary function is
`2 T-density − (r·∇V)-density`. -/
private lemma hasDerivAt_virialAux
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x) (x : ℝ) :
    HasDerivAt (virialAux c E u u' V)
      (2 * c * ‖u' x‖ ^ 2 - x * V' x * ‖u x‖ ^ 2) x := by
  have hK := (hasDerivAt_normSq_deriv hu' x).const_mul c
  have hN := hasDerivAt_normSq hu x
  have hVE : HasDerivAt (fun t => (V t - E) * ‖u t‖ ^ 2)
      (V' x * ‖u x‖ ^ 2 + (V x - E) * (2 * ⟪u x, u' x⟫)) x := ((hV x).sub_const E).mul hN
  have hF := hK.sub hVE
  have hxF := (hasDerivAt_id x).mul hF
  have hP := (hasDerivAt_inner_u_u' hu hu' x).const_mul c
  have h := hxF.add hP
  have hA := inner_u_u'' hSch x
  have hB := inner_u'_u'' hSch x
  convert h using 1
  simp only [id_eq]
  linear_combination (-(2 : ℝ) * x) * hB - hA

/-- The auxiliary function vanishes at infinity for a bound state. -/
private lemma tendsto_virialAux {l : Filter ℝ}
    (hd1 : Tendsto (fun x => x * ‖u' x‖ ^ 2) l (𝓝 0))
    (hd2 : Tendsto (fun x => x * ((V x - E) * ‖u x‖ ^ 2)) l (𝓝 0))
    (hd3 : Tendsto (fun x => (⟪u x, u' x⟫ : ℝ)) l (𝓝 0)) :
    Tendsto (virialAux c E u u' V) l (𝓝 0) := by
  have h := ((hd1.const_mul c).sub hd2).add (hd3.const_mul c)
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr (fun t => ?_)
  simp only [virialAux]
  ring

/-- Boundary term of the "kinetic" integration by parts vanishes. -/
private lemma tendsto_inner_smul {l : Filter ℝ}
    (hd3 : Tendsto (fun x => (⟪u x, u' x⟫ : ℝ)) l (𝓝 0)) :
    Tendsto (fun t => c * ⟪u t, u' t⟫) l (𝓝 0) := by
  simpa using hd3.const_mul c

/-- **Kinetic energy identity.** For a bound stationary state,
`⟨T⟩ = c ∫ ‖u'‖²`, i.e. the expectation of `-c d²/dx²` equals the Dirichlet energy. -/
private lemma kinetic_expectation
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x)
    (hNint : Integrable (fun x => ‖u x‖ ^ 2))
    (hVint : Integrable (fun x => V x * ‖u x‖ ^ 2))
    (hKint : Integrable (fun x => ‖u' x‖ ^ 2))
    (hd3top : Tendsto (fun x => (⟪u x, u' x⟫ : ℝ)) atTop (𝓝 0))
    (hd3bot : Tendsto (fun x => (⟪u x, u' x⟫ : ℝ)) atBot (𝓝 0)) :
    ∫ x, (⟪u x, -(c : ℂ) * u'' x⟫ : ℝ) = c * ∫ x, ‖u' x‖ ^ 2 := by
  -- the integrand `(V - E)‖u‖² + c‖u'‖²` is a derivative of a function vanishing at ±∞
  have hVEint : Integrable (fun x => (V x - E) * ‖u x‖ ^ 2) := by
    have : Integrable (fun x => V x * ‖u x‖ ^ 2 - E * ‖u x‖ ^ 2) :=
      hVint.sub (hNint.const_mul E)
    exact this.congr (by filter_upwards with x; ring)
  have hint : Integrable (fun x => (V x - E) * ‖u x‖ ^ 2 + c * ‖u' x‖ ^ 2) :=
    hVEint.add (hKint.const_mul c)
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t => c * ⟪u t, u' t⟫)
      ((V x - E) * ‖u x‖ ^ 2 + c * ‖u' x‖ ^ 2) x := by
    intro x
    have h := (hasDerivAt_inner_u_u' hu hu' x).const_mul c
    have hA := inner_u_u'' hSch x
    convert h using 1
    linear_combination -hA
  have hzero : ∫ x, ((V x - E) * ‖u x‖ ^ 2 + c * ‖u' x‖ ^ 2) = 0 := by
    have := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hint
      (tendsto_inner_smul hd3bot) (tendsto_inner_smul hd3top)
    simpa using this
  rw [integral_add hVEint (hKint.const_mul c), integral_const_mul] at hzero
  have hTeq : ∫ x, (⟪u x, -(c : ℂ) * u'' x⟫ : ℝ) = ∫ x, -((V x - E) * ‖u x‖ ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hA := inner_u_u'' hSch x
    have : ((-(c : ℂ)) * u'' x) = (-c : ℝ) • u'' x := by
      rw [Complex.real_smul]; push_cast; ring
    rw [this, real_inner_smul_right]
    linear_combination -hA
  rw [hTeq, integral_neg]
  linarith [hzero]

/-- **Quantum virial theorem (one dimension).**

Let `u` be a bound stationary state of the Hamiltonian `H ψ = -c ψ'' + V ψ`
(with `c = ℏ²/(2m)`), i.e. `-c u'' + V u = E u`, normalized to `∫ ‖u‖² = 1`,
with the boundary/decay behaviour of a bound state.  Then

`2 ⟨T⟩ = ⟨r · ∇V⟩`,

where `⟨T⟩ = ∫ ⟪u, (-c) u''⟫` is the expectation of the kinetic energy operator and
`⟨r · ∇V⟩ = ∫ x V'(x) ‖u x‖²`.

(The normalization hypothesis `hnorm` is stated because `⟨·⟩` denotes an expectation value of a
normalized state; the identity itself is homogeneous and does not use it.) -/
theorem virial_theorem
    {c E : ℝ} {u u' u'' : ℝ → ℂ} {V V' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x)
    (hnorm : ∫ x, ‖u x‖ ^ 2 = 1)
    (hNint : Integrable (fun x => ‖u x‖ ^ 2))
    (hVint : Integrable (fun x => V x * ‖u x‖ ^ 2))
    (hKint : Integrable (fun x => ‖u' x‖ ^ 2))
    (hWint : Integrable (fun x => x * V' x * ‖u x‖ ^ 2))
    (hd1top : Tendsto (fun x => x * ‖u' x‖ ^ 2) atTop (𝓝 0))
    (hd1bot : Tendsto (fun x => x * ‖u' x‖ ^ 2) atBot (𝓝 0))
    (hd2top : Tendsto (fun x => x * ((V x - E) * ‖u x‖ ^ 2)) atTop (𝓝 0))
    (hd2bot : Tendsto (fun x => x * ((V x - E) * ‖u x‖ ^ 2)) atBot (𝓝 0))
    (hd3top : Tendsto (fun x => (⟪u x, u' x⟫ : ℝ)) atTop (𝓝 0))
    (hd3bot : Tendsto (fun x => (⟪u x, u' x⟫ : ℝ)) atBot (𝓝 0)) :
    2 * ∫ x, (⟪u x, -(c : ℂ) * u'' x⟫ : ℝ) = ∫ x, x * V' x * ‖u x‖ ^ 2 := by
  have hint : Integrable (fun x => 2 * c * ‖u' x‖ ^ 2 - x * V' x * ‖u x‖ ^ 2) :=
    (hKint.const_mul (2 * c)).sub hWint
  have hzero : ∫ x, (2 * c * ‖u' x‖ ^ 2 - x * V' x * ‖u x‖ ^ 2) = 0 := by
    have := MeasureTheory.integral_of_hasDerivAt_of_tendsto
      (hasDerivAt_virialAux hu hu' hV hSch) hint
      (tendsto_virialAux hd1bot hd2bot hd3bot) (tendsto_virialAux hd1top hd2top hd3top)
    simpa using this
  rw [integral_sub (hKint.const_mul (2 * c)) hWint, integral_const_mul, sub_eq_zero] at hzero
  rw [kinetic_expectation hu hu' hSch hNint hVint hKint hd3top hd3bot, ← hzero]
  ring

end Virial

end Phys

