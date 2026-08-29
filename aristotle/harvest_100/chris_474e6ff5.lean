/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

namespace Phys

/-! ## Setting

We formalise Bekenstein's gedanken derivation of the universal entropy bound.

A weakly gravitating system of total energy `E` fits inside a sphere of radius `R` and
carries entropy `S`.  It is lowered into a Schwarzschild black hole of mass `M` by the
Geroch process: when the box is released at proper distance `R` above the horizon the
gravitational redshift factor is `R / (2 r_s)` with `r_s = 2 G M / c ^ 2`, so the mass
delivered to the hole is

  `ΔM = E * R / (4 * G * M)`.

The Bekenstein–Hawking entropy of a Schwarzschild hole of mass `m` is

  `S_BH m = k c ^ 3 A / (4 G ℏ) = 4 π k G m ^ 2 / (ℏ c)`,   `A = 16 π G ^ 2 m ^ 2 / c ^ 4`.

The (leading order) entropy gained by the hole is `S_BH' M * ΔM`, and the generalised
second law demands that this be at least the entropy `S` that disappeared behind the
horizon.  Algebra then yields exactly the Bekenstein bound `S ≤ 2 π k R E / (ℏ c)`.
-/

/-- Bekenstein–Hawking entropy `4 π k G m ^ 2 / (ℏ c)` of a Schwarzschild black hole of
mass `m`, in terms of Boltzmann's constant `k`, the reduced Planck constant `hbar`,
the speed of light `c` and Newton's constant `G`. -/
noncomputable def bhEntropy (k hbar c G : ℝ) (m : ℝ) : ℝ :=
  4 * Real.pi * k * G * m ^ 2 / (hbar * c)

/-- Mass delivered to a black hole of mass `M` by the Geroch process, when a box of
energy `E` and size `R` is released at proper distance `R` above the horizon:
the redshift factor `R / (2 r_s)`, `r_s = 2 G M / c ^ 2`, applied to `E / c ^ 2`. -/
noncomputable def gerochDeliveredMass (G M R E : ℝ) : ℝ := E * R / (4 * G * M)

/-- The derivative of the Bekenstein–Hawking entropy with respect to the black hole mass. -/
lemma deriv_bhEntropy (k hbar c G M : ℝ) :
    deriv (bhEntropy k hbar c G) M = 8 * Real.pi * k * G * M / (hbar * c) := by
  have h : bhEntropy k hbar c G = fun m => (4 * Real.pi * k * G / (hbar * c)) * m ^ 2 := by
    funext m
    unfold bhEntropy
    ring
  rw [h, deriv_const_mul _ (by fun_prop)]
  simp
  ring

/-- The key computation: the entropy that a Schwarzschild black hole of mass `M` gains
(to leading order) in the Geroch process is exactly `2 π k R E / (ℏ c)`, independently
of `M` and of Newton's constant `G`. -/
theorem gerochEntropyGain_eq (k hbar c G M R E : ℝ) (hG : G ≠ 0) (hM : M ≠ 0) :
    deriv (bhEntropy k hbar c G) M * gerochDeliveredMass G M R E
      = 2 * Real.pi * k * R * E / (hbar * c) := by
  rw [deriv_bhEntropy]
  unfold gerochDeliveredMass
  rcases eq_or_ne (hbar * c) 0 with h | h
  · rw [h]
    simp
  · field_simp
    ring

/-- **Bekenstein bound.**  For a system of energy `E` contained in a sphere of radius `R`,
the entropy `S` obeys `S ≤ 2 π k R E / (ℏ c)`.

The bound is derived, as by Bekenstein, from the generalised second law applied to the
Geroch process: hypothesis `hGSL` says that the entropy `S` swallowed by a Schwarzschild
black hole of mass `M` is at most the entropy `deriv (bhEntropy k hbar c G) M * ΔM` that
the hole gains from the delivered mass `ΔM = gerochDeliveredMass G M R E`. -/
theorem bekenstein_bound
    (k hbar c G M R E S : ℝ) (hG : 0 < G) (hM : 0 < M)
    (hGSL : S ≤ deriv (bhEntropy k hbar c G) M * gerochDeliveredMass G M R E) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) := by
  rwa [gerochEntropyGain_eq k hbar c G M R E hG.ne' hM.ne'] at hGSL

end Phys

