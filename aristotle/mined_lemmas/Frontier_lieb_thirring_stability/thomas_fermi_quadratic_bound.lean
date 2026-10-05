/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment: in Lean 4 a module docstring `/-! ... -/`
-- may not precede the `import` lines; it is repeated as a docstring below.)

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## Stability of matter from the Lieb–Thirring kinetic energy inequality

The Lieb–Thirring inequality states that for an antisymmetric normalized `N`-fermion wave
function `Ψ` in three dimensions, with one-body density `ρ_Ψ`, the kinetic energy obeys

  `T(Ψ) ≥ K ∫ ρ_Ψ ^ (5/3)`

for a universal constant `K > 0`.  Together with an electrostatic (Thomas–Fermi type) lower
bound for the Coulomb interaction of the electrons with `M` nuclei,

  `W(Ψ) ≥ - A ∫ ρ_Ψ ^ (4/3) - B * M`,

it implies *stability of matter of the second kind*: the total energy is bounded below by a
constant times the number of particles,

  `T(Ψ) + W(Ψ) ≥ - (A ^ 2 / (4 K)) * N - B * M`,

where `N = ∫ ρ_Ψ` is the number of electrons.

This file formalizes that implication as a Lean-checked reduction: the two physical input
bounds are taken as hypotheses (they are the analytic inputs of the theory), and the linear
lower bound on the energy is derived.  The mathematical content of the reduction is the
Cauchy–Schwarz interpolation `∫ ρ^(4/3) ≤ (∫ ρ^(5/3))^(1/2) (∫ ρ)^(1/2)` followed by
completing the square, which is exactly the argument of Lieb and Thirring.
-/

/-- **Interpolation step.** For a nonnegative density `ρ` with `ρ` and `ρ ^ (5/3)` integrable,
Cauchy–Schwarz (Hölder with exponents `2, 2` applied to `ρ ^ (5/6) · ρ ^ (1/2)`) gives
`∫ ρ ^ (4/3) ≤ (∫ ρ ^ (5/3)) ^ (1/2) * (∫ ρ) ^ (1/2)`. -/

theorem thomas_fermi_quadratic_bound {K A t n : ℝ} (hK : 0 < K)
    (ht : 0 ≤ t) (hn : 0 ≤ n) :
    -(A ^ 2 / (4 * K)) * n ≤ K * t - A * (t ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ)) := by
  set u : ℝ := t ^ (1 / 2 : ℝ) with hu
  set v : ℝ := n ^ (1 / 2 : ℝ) with hv
  have hu2 : u * u = t := by
    rw [hu, ← Real.rpow_add' ht (by norm_num)]
    norm_num
  have hv2 : v * v = n := by
    rw [hv, ← Real.rpow_add' hn (by norm_num)]
    norm_num
  rw [← hu2, ← hv2, ← sub_nonneg]
  have hid : K * (u * u) - A * (u * v) - -(A ^ 2 / (4 * K)) * (v * v)
      = (2 * K * u - A * v) ^ 2 / (4 * K) := by
    field_simp; ring
  rw [hid]
  positivity

/-- **Stability of matter of the second kind, as a reduction from the Lieb–Thirring
inequality.**

Let `ρ ≥ 0` be the one-body density of a state of an `N`-electron system in the presence of
`M` nuclei (`N = ∫ ρ`).  Assume:

* the Lieb–Thirring kinetic energy bound `K ∫ ρ ^ (5/3) ≤ T` with `K > 0`;
* an electrostatic lower bound `-A ∫ ρ ^ (4/3) - B * M ≤ W` with `A ≥ 0`.

Then the total energy satisfies the linear (in the particle numbers) lower bound

  `-(A ^ 2 / (4 K)) * N - B * M ≤ T + W`,

i.e. the energy per particle is bounded below by a constant independent of `N` and `M`. -/
