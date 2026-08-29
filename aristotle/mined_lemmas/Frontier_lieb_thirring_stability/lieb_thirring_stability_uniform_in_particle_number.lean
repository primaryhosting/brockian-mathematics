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

theorem lieb_thirring_stability_uniform_in_particle_number {ι : Type*} (K : ℝ) (hK : 0 < K)
    (s : Finset ι) (w V : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hV : ∀ i ∈ s, 0 ≤ V i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ρ : ι → ℝ) (T : ℝ), (∀ i ∈ s, 0 ≤ ρ i) →
      ∑ i ∈ s, w i * ρ i = (N : ℝ) → LiebThirringKinetic K s w ρ T →
      -C ≤ energy T s w V ρ := by
  refine ⟨tfConst K * ∑ i ∈ s, w i * V i ^ (5 / 2 : ℝ), ?_, ?_⟩
  · have h1 : 0 ≤ tfConst K := by
      rw [tfConst]
      positivity
    have h2 : 0 ≤ ∑ i ∈ s, w i * V i ^ (5 / 2 : ℝ) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hV i hi) _)
    exact mul_nonneg h1 h2
  · intro _ ρ T hρ _ hT
    have := lieb_thirring_stability K hK s w ρ V T hw hρ hV hT
    linarith [this]

/-- **The stability bound is attained**, hence non-vacuous and sharp: for the one-site
system with unit weight and unit potential there is a density `ρ` and a kinetic energy `T`
saturating both the Lieb–Thirring hypothesis and the conclusion of
`lieb_thirring_stability`. -/
