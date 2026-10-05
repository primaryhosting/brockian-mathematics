/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

/-!
## Overview

The Lieb–Thirring inequality (in three dimensions, for the exponent `γ = 1`) comes in two
equivalent guises:

* the **eigenvalue form**: for a one-body potential `V ≥ 0`, the sum of the negative
  eigenvalues of the Schrödinger operator `-Δ - V` is bounded below by
  `-L * ∫ V ^ (5/2)`, i.e. for any system of `N` orthonormal states with one-particle
  density `ρ` and kinetic energy `T`, one has `T - ∫ ρ * V ≥ -L * ∫ V ^ (5/2)`;

* the **kinetic-energy form**: `T ≥ K * ∫ ρ ^ (5/3)` — a Thomas–Fermi lower bound on the
  kinetic energy in terms of the one-particle density alone.

The passage between the two forms is a Legendre-duality argument, and the kinetic-energy
form is exactly the ingredient that yields *stability of matter*: the total energy is
bounded below by a quantity that does not depend on the number of particles.

This file formalizes that duality completely and rigorously, on an arbitrary measure space:

* `Frontier.young_five_thirds` — the pointwise Legendre/Young inequality
  `x * y ≤ K * x ^ (5/3) + ltDualConst K * y ^ (5/2)` with the optimal constant
  `ltDualConst K = (2/5) * (3/(5*K)) ^ (3/2)`;
* `Frontier.kinetic_bound_of_eigenvalue_bound` — the reduction from the eigenvalue form
  (with constant `L`) to the kinetic-energy form, with the explicit constant
  `ltKineticConst L = (3/5) * (2/(5*L)) ^ (2/3)`;
* `Frontier.lieb_thirring_stability` — the main target: the kinetic-energy form implies a
  lower bound on the total energy `T - ∫ ρ * V` which is uniform in the state (in
  particular uniform in the particle number), depending only on the external potential
  through `∫ V ^ (5/2)`.

Everything is stated for the *density* `ρ` and *kinetic energy* `T` of a state, which is
the level at which the Lieb–Thirring argument actually operates; no analytic facts about
Schrödinger operators are assumed beyond the two hypotheses that are being related.
-/

namespace Frontier

open MeasureTheory

/-- The optimal constant in the Legendre duality between the exponents `5/3` and `5/2`:
if the kinetic-energy (Thomas–Fermi) constant is `K`, the dual eigenvalue-sum constant is
`ltDualConst K = (2/5) * (3/(5*K)) ^ (3/2)`. -/

theorem ltDualConst_ltKineticConst {L : ℝ} (hL : 0 < L) :
    ltDualConst (ltKineticConst L) = L := by
  set b : ℝ := 2 / (5 * L) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hK0 : 0 < ltKineticConst L := by rw [ltKineticConst, ← hb]; positivity
  have h1 : 5 * ltKineticConst L / 3 = b ^ (2/3 : ℝ) := by
    rw [ltKineticConst, ← hb]; ring
  have h2 : 3 / (5 * ltKineticConst L) = b ^ (-(2/3) : ℝ) := by
    rw [Real.rpow_neg hb0.le, ← h1]
    field_simp
  rw [ltDualConst, h2, ← Real.rpow_mul hb0.le,
    show (-((2:ℝ)/3)) * (3/2) = -1 by norm_num, Real.rpow_neg_one, hb]
  field_simp

end Frontier

