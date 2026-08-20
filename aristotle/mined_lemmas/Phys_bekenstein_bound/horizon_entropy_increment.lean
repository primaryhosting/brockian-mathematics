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

/--
Data for Bekenstein's *Geroch-process* derivation of the universal entropy bound.

A material body of total energy `E`, radius `R` and thermodynamic entropy `S` is slowly
lowered into a Schwarzschild black hole of mass `M` and then dropped in once its centre of
mass sits one proper radius `R` above the horizon.  The fields below record the physical
input of the argument:

* `hDeltaM` : the energy actually delivered to the hole is the gravitationally redshifted
  energy `E * R / (2 * r_s) = E * R * c ^ 2 / (4 * G * M)` (with `r_s = 2 G M / c ^ 2` the
  Schwarzschild radius and the redshift factor `√(1 - r_s/r) ≈ ℓ / (2 r_s)` at proper
  height `ℓ = R`), so the mass increment is `ΔM = E * R / (4 * G * M)`.

* `hDeltaS` : the Bekenstein–Hawking entropy of the hole is
  `S_BH = k c ^ 3 A / (4 G ℏ) = 4 π k G M ^ 2 / (ℏ c)`, whose increment to first order in
  the mass increment is `ΔS_BH = (8 π k G M / (ℏ c)) * ΔM`.

* `hGSL` : the generalized second law — the body's entropy `S` is lost to the exterior
  world, so the horizon entropy must increase by at least `S`.
-/
structure BekensteinSetup where
  /-- Boltzmann's constant. -/
  k : ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- Speed of light. -/
  c : ℝ
  /-- Newton's gravitational constant. -/
  G : ℝ
  /-- Mass of the Schwarzschild black hole used as the entropy accountant. -/
  M : ℝ
  /-- Total energy of the body. -/
  E : ℝ
  /-- Radius of the body. -/
  R : ℝ
  /-- Thermodynamic entropy of the body. -/
  S : ℝ
  /-- Mass increment acquired by the black hole. -/
  dM : ℝ
  /-- Entropy increment of the black hole. -/
  dS : ℝ
  hbar_pos : 0 < hbar
  c_pos : 0 < c
  G_pos : 0 < G
  M_pos : 0 < M
  /-- Redshifted energy delivered at proper height `R` above the horizon. -/
  hDeltaM : dM = E * R / (4 * G * M)
  /-- First-order variation of the Bekenstein–Hawking entropy `4 π k G M ^ 2 / (ℏ c)`. -/
  hDeltaS : dS = 8 * Real.pi * k * G * M / (hbar * c) * dM
  /-- Generalized second law. -/
  hGSL : S ≤ dS

namespace BekensteinSetup

variable (T : BekensteinSetup)

/--
**Key lemma.**  The black hole's entropy increment in the Geroch process is *exactly*
`2 π k R E / (ℏ c)`: the mass `M` of the accountant black hole cancels between the
redshift factor and the derivative of the Bekenstein–Hawking entropy.
-/

theorem horizon_entropy_increment :
    T.dS = 2 * Real.pi * T.k * T.R * T.E / (T.hbar * T.c) := by
  have hhbar := T.hbar_pos.ne'
  have hc := T.c_pos.ne'
  have hG := T.G_pos.ne'
  have hM := T.M_pos.ne'
  rw [T.hDeltaS, T.hDeltaM]
  field_simp
  ring

end BekensteinSetup

/--
**Bekenstein bound.**  For a body of energy `E` contained in a sphere of radius `R`, the
thermodynamic entropy obeys
`S ≤ 2 π k R E / (ℏ c)`.

The proof is Bekenstein's Geroch-process argument: by the generalized second law the
entropy `S` lost when the body falls through the horizon must be compensated by the
increase of the Bekenstein–Hawking entropy, and that increase equals `2 π k R E / (ℏ c)`
by `Phys.BekensteinSetup.horizon_entropy_increment`.
-/
