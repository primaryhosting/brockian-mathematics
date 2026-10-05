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
