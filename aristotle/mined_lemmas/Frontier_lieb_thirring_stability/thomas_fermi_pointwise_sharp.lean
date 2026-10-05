/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
## Lieb–Thirring and stability of matter

The Lieb–Thirring kinetic energy inequality states that, for an antisymmetric `N`-particle
wave function in three dimensions with one-particle density `ρ`, the kinetic energy obeys

  `T ≥ K ∫ ρ(x) ^ (5/3) dx`

with a constant `K > 0` that is *independent of the particle number* `N`.  Stability of
matter is deduced from this by combining it with the electrostatic (one-body) energy
`- ∫ V ρ` via the Thomas–Fermi bound: the resulting energy functional is bounded below by
`- C(K) ∫ V ^ (5/2)`, again uniformly in `N`.

This file formalizes that deduction — the Lieb–Thirring ⇒ stability reduction — in a
discretized (quadrature) form, in which integrals are replaced by finite weighted sums
`∑ i ∈ s, w i * f i` with nonnegative weights `w`.  The Lieb–Thirring kinetic bound is a
hypothesis (`Frontier.LiebThirringKinetic`), and everything else is proved:

* `Frontier.thomas_fermi_pointwise`  : the pointwise Young/Thomas–Fermi inequality
  `V * t ≤ K * t ^ (5/3) + tfConst K * V ^ (5/2)`;
* `Frontier.thomas_fermi_pointwise_sharp` : the constant `tfConst K` in it is optimal;
* `Frontier.lieb_thirring_stability` : the resulting lower bound on the energy;
* `Frontier.lieb_thirring_stability_uniform_in_particle_number` : the same bound, stated
  for a density normalized to `N` particles, with a right-hand side that does not depend
  on `N` — this uniformity is the content of stability of matter.
-/

namespace Frontier

/-- The Thomas–Fermi constant associated with a Lieb–Thirring constant `K`:
`tfConst K = (2/5) * (3/5) ^ (3/2) * K ^ (-3/2)`.  It is the sharp constant in
`V * t ≤ K * t ^ (5/3) + tfConst K * V ^ (5/2)` (see `thomas_fermi_pointwise`), i.e.

  `min_{t ≥ 0} (K * t ^ (5/3) - V * t) = - tfConst K * V ^ (5/2)`. -/

theorem thomas_fermi_pointwise_sharp (K V : ℝ) (hK : 0 < K) (hV : 0 ≤ V) :
    ∃ t : ℝ, 0 ≤ t ∧ V * t = K * t ^ (5 / 3 : ℝ) + tfConst K * V ^ (5 / 2 : ℝ) := by
  rcases eq_or_lt_of_le hV with h0 | hVpos
  · refine ⟨0, le_rfl, ?_⟩
    simp [← h0, Real.zero_rpow, tfConst]
  refine ⟨(3 * V / (5 * K)) ^ (3 / 2 : ℝ), Real.rpow_nonneg (by positivity) _, ?_⟩
  set B : ℝ := 3 * V / (5 * K) with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have e1 : (B ^ (3 / 2 : ℝ)) ^ (5 / 3 : ℝ) = B ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_mul hBpos.le]; norm_num
  have e2 : B ^ (5 / 2 : ℝ) = B ^ (3 / 2 : ℝ) * B := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hBpos, Real.rpow_one]
  have e3 : B ^ (3 / 2 : ℝ) = (3 / 5 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2) : ℝ) * V ^ (3 / 2 : ℝ) := by
    rw [hB, show (3 * V / (5 * K) : ℝ) = (3 / 5 : ℝ) * V * K⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hV,
      ← Real.rpow_neg_one K, ← Real.rpow_mul hK.le]
    ring_nf
  have e4 : V ^ (5 / 2 : ℝ) = V ^ (3 / 2 : ℝ) * V := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hVpos, Real.rpow_one]
  rw [e1, e2, tfConst, e3, e4]
  have hKB : K * B = 3 * V / 5 := by rw [hB]; field_simp
  linear_combination
    (-((3 / 5 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2) : ℝ) * V ^ (3 / 2 : ℝ))) * hKB

/-- **Stability from the Lieb–Thirring inequality.**  If the kinetic energy `T` of a state
with one-particle density `ρ` satisfies the Lieb–Thirring bound with constant `K > 0`, then
the total energy `T - ∑ w V ρ` in the attractive potential `-V` is bounded below by
`- tfConst K * ∑ w * V ^ (5/2)`.  The bound depends only on `K` and on the potential — not
on the state, and in particular not on the number of particles. -/
