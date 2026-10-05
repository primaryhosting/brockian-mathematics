import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option grind.warning false

namespace Phys

open MeasureTheory Filter Topology

/-- The (unnormalized) kinetic energy density `ψ* (T ψ)` of a one-dimensional
wave function `ψ` with second derivative `ψ2`, for a particle of mass `m`
(in units with `ℏ = 1`), i.e. `T = -(1/2m) d²/dx²`. -/
noncomputable def kineticDensity (m : ℝ) (ψ ψ2 : ℝ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (ψ x) * (-(1 / (2 * m)) * ψ2 x)

/-- The (unnormalized) virial density `ψ* (x V'(x)) ψ`, i.e. the integrand of
the expectation value `⟨r · ∇V⟩` in one dimension, where `V1` is the derivative
of the potential `V`. -/
noncomputable def virialDensity (V1 : ℝ → ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (ψ x) * (((x * V1 x : ℝ) : ℂ) * ψ x)

/-- The boundary flux associated with the virial operator `A = x d/dx`.  It is the
quantity whose derivative is `2 * (kinetic density) - (virial density)`; for a bound
state it decays to `0` at `±∞`, which is what makes the virial theorem hold.

Explicitly, `virialFlux m E V ψ ψ1 x =
  -(1/2m) ψ*(x) ψ'(x) + x ((1/2m) |ψ'(x)|² - (V(x) - E) |ψ(x)|²)`. -/
noncomputable def virialFlux (m E : ℝ) (V : ℝ → ℝ) (ψ ψ1 : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(1 / (2 * m)) * (starRingEnd ℂ) (ψ x) * ψ1 x
    + (x : ℂ) * ((1 / (2 * m)) * (starRingEnd ℂ) (ψ1 x) * ψ1 x
        - (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ x) * ψ x)

/-- From the time-independent Schrödinger equation, the second derivative of `ψ`
is `2m (V - E) ψ`. -/
theorem second_deriv_eq_of_schrodinger {m E : ℝ} (hm : m ≠ 0) {V : ℝ → ℝ} {ψ ψ2 : ℝ → ℂ}
    (hSch : ∀ x, -(1 / (2 * m)) * ψ2 x + ((V x : ℝ) : ℂ) * ψ x = (E : ℂ) * ψ x) :
    ∀ x, ψ2 x = 2 * (m : ℂ) * (((V x : ℝ) : ℂ) - (E : ℂ)) * ψ x := by
  intro x
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h := hSch x
  field_simp at h
  linear_combination -h

/-- The key pointwise identity: the derivative of the virial boundary flux equals
`2 * (kinetic density) - (virial density)`. -/
theorem hasDerivAt_virialFlux {m E : ℝ} (hm : m ≠ 0) {V V1 : ℝ → ℝ} {ψ ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : ∀ x, HasDerivAt ψ (ψ1 x) x)
    (hψ2 : ∀ x, HasDerivAt ψ1 (ψ2 x) x)
    (hV1 : ∀ x, HasDerivAt V (V1 x) x)
    (hSch : ∀ x, -(1 / (2 * m)) * ψ2 x + ((V x : ℝ) : ℂ) * ψ x = (E : ℂ) * ψ x) (x : ℝ) :
    HasDerivAt (virialFlux m E V ψ ψ1)
      (2 * kineticDensity m ψ ψ2 x - virialDensity V1 ψ x) x := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hψ2eq := second_deriv_eq_of_schrodinger hm hSch
  -- basic derivatives
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hVc : HasDerivAt (fun t : ℝ => ((V t : ℝ) : ℂ)) ((V1 x : ℝ) : ℂ) x :=
    (hV1 x).ofReal_comp
  have hcψ : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (ψ t)) ((starRingEnd ℂ) (ψ1 x)) x :=
    (hψ1 x).star
  have hcψ1 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (ψ1 t)) ((starRingEnd ℂ) (ψ2 x)) x :=
    (hψ2 x).star
  have key :
      HasDerivAt (virialFlux m E V ψ ψ1)
        ((-(1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ1 x) * ψ1 x
            + -(1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ x) * ψ2 x)
          + (1 * ((1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ1 x) * ψ1 x
                - (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ x) * ψ x)
            + (x : ℂ) * (((1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ2 x) * ψ1 x
                  + (1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ1 x) * ψ2 x)
                - ((((V1 x : ℝ) : ℂ) * (starRingEnd ℂ) (ψ x) * ψ x
                      + (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ1 x) * ψ x)
                    + (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ x) * ψ1 x)))) x := by
    have h1 : HasDerivAt (fun t : ℝ => -(1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ t) * ψ1 t)
        (-(1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ1 x) * ψ1 x
          + -(1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ x) * ψ2 x) x := by
      exact ((hcψ.const_mul (-(1 / (2 * (m : ℂ))))).mul (hψ2 x)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ => (1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ1 t) * ψ1 t)
        ((1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ2 x) * ψ1 x
          + (1 / (2 * (m : ℂ))) * (starRingEnd ℂ) (ψ1 x) * ψ2 x) x := by
      exact ((hcψ1.const_mul (1 / (2 * (m : ℂ)))).mul (hψ2 x)).congr_deriv (by ring)
    have h3 : HasDerivAt
        (fun t : ℝ => (((V t : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ t) * ψ t)
        ((((V1 x : ℝ) : ℂ) * (starRingEnd ℂ) (ψ x) * ψ x
            + (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ1 x) * ψ x)
          + (((V x : ℝ) : ℂ) - (E : ℂ)) * (starRingEnd ℂ) (ψ x) * ψ1 x) x := by
      exact (((hVc.sub_const (E : ℂ)).mul hcψ).mul (hψ1 x)).congr_deriv (by
        simp only [Pi.mul_apply]; ring)
    exact h1.add (hx.mul (h2.sub h3))
  refine key.congr_deriv ?_
  simp only [kineticDensity, virialDensity, hψ2eq, map_mul, map_sub, map_ofNat,
    Complex.conj_ofReal, Complex.ofReal_mul]
  field_simp
  ring

/-- **Quantum virial theorem** (one dimension, `ℏ = 1`).

Let `ψ : ℝ → ℂ` be a stationary state of energy `E` for a particle of mass `m ≠ 0`
in a real potential `V`, i.e. `ψ` has first derivative `ψ1`, second derivative `ψ2`,
and satisfies the time-independent Schrödinger equation
`-(1/2m) ψ'' + V ψ = E ψ`.  Assume `ψ` is a *bound* state in the sense that the
virial boundary flux `virialFlux` tends to `0` at `±∞`, and that the kinetic and
virial densities are integrable.

Then `2 ⟨T⟩ = ⟨x · V'(x)⟩`. -/
theorem virial_theorem {m E : ℝ} (hm : m ≠ 0) {V V1 : ℝ → ℝ} {ψ ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : ∀ x, HasDerivAt ψ (ψ1 x) x)
    (hψ2 : ∀ x, HasDerivAt ψ1 (ψ2 x) x)
    (hV1 : ∀ x, HasDerivAt V (V1 x) x)
    (hSch : ∀ x, -(1 / (2 * m)) * ψ2 x + ((V x : ℝ) : ℂ) * ψ x = (E : ℂ) * ψ x)
    (hTint : Integrable (kineticDensity m ψ ψ2))
    (hWint : Integrable (virialDensity V1 ψ))
    (hbot : Tendsto (virialFlux m E V ψ ψ1) atBot (𝓝 0))
    (htop : Tendsto (virialFlux m E V ψ ψ1) atTop (𝓝 0)) :
    2 * ∫ x, kineticDensity m ψ ψ2 x = ∫ x, virialDensity V1 ψ x := by
  have hInt : Integrable
      (fun x => 2 * kineticDensity m ψ ψ2 x - virialDensity V1 ψ x) :=
    (hTint.const_mul 2).sub hWint
  have hzero : ∫ x, (2 * kineticDensity m ψ ψ2 x - virialDensity V1 ψ x) = 0 := by
    have := integral_of_hasDerivAt_of_tendsto
      (hasDerivAt_virialFlux hm hψ1 hψ2 hV1 hSch) hInt hbot htop
    simpa using this
  rw [integral_sub (hTint.const_mul 2) hWint, integral_const_mul] at hzero
  linear_combination hzero

end Phys

