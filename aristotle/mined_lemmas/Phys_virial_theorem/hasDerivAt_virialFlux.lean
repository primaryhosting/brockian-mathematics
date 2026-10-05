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
