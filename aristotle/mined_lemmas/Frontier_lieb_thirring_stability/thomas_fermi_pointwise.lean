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

theorem thomas_fermi_pointwise (K t V : ℝ) (hK : 0 < K) (ht : 0 ≤ t) (hV : 0 ≤ V) :
    V * t ≤ K * t ^ (5 / 3 : ℝ) + tfConst K * V ^ (5 / 2 : ℝ) := by
  rw [tfConst]
  set a : ℝ := (5 * K / 3) ^ (3 / 5 : ℝ) with ha
  have hbase : (0 : ℝ) < 5 * K / 3 := by positivity
  have hapos : 0 < a := Real.rpow_pos_of_pos hbase _
  have hy : (5 / 3 : ℝ).HolderConjugate (5 / 2) := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := Real.young_inequality (a * t) (V / a) hy
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  have hmul : (a * t) * (V / a) = V * t := by field_simp
  rw [hmul, Real.mul_rpow hapos.le ht, Real.div_rpow hV hapos.le] at h
  have h1 : a ^ (5 / 3 : ℝ) = 5 * K / 3 := by
    rw [ha, ← Real.rpow_mul hbase.le]; norm_num
  have h2 : a ^ (5 / 2 : ℝ) = (5 / 3 : ℝ) ^ (3 / 2 : ℝ) * K ^ (3 / 2 : ℝ) := by
    rw [ha, ← Real.rpow_mul hbase.le]
    norm_num
    rw [show (5 * K / 3 : ℝ) = (5 / 3 : ℝ) * K by ring, Real.mul_rpow (by norm_num) hK.le]
  have h3 : (3 / 5 : ℝ) ^ (3 / 2 : ℝ) = ((5 / 3 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [← Real.inv_rpow (by norm_num)]; norm_num
  have h4 : K ^ (-(3 / 2) : ℝ) = (K ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hK.le _
  rw [h1, h2] at h
  rw [h3, h4]
  have hK32 : (0 : ℝ) < K ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hK _
  have h53 : (0 : ℝ) < (5 / 3 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  calc V * t
      ≤ 5 * K / 3 * t ^ (5 / 3 : ℝ) / (5 / 3)
          + V ^ (5 / 2 : ℝ) / ((5 / 3 : ℝ) ^ (3 / 2 : ℝ) * K ^ (3 / 2 : ℝ)) / (5 / 2) := h
    _ = K * t ^ (5 / 3 : ℝ)
          + 2 / 5 * ((5 / 3 : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (K ^ (3 / 2 : ℝ))⁻¹ * V ^ (5 / 2 : ℝ) := by
        field_simp

/-- **Sharpness of the Thomas–Fermi constant.**  The inequality
`thomas_fermi_pointwise` is an equality at `t = (3 * V / (5 * K)) ^ (3/2)`, so
`tfConst K` cannot be lowered. -/
