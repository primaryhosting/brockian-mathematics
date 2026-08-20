/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

namespace Frontier

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/

theorem linear_lower_of_deriv_ge (M dM : ℝ → ℝ) (βc c0 : ℝ) (hM0 : M βc = 0)
    (hc : ContinuousOn M (Set.Ici βc))
    (hd : ∀ β, βc < β → HasDerivAt M (dM β) β)
    (hge : ∀ β, βc < β → c0 ≤ dM β) :
    ∀ β, βc ≤ β → c0 * (β - βc) ≤ M β := by
  intro β hβ
  have hint : interior (Set.Ici βc) = Set.Ioi βc := interior_Ici
  have hdiff : DifferentiableOn ℝ M (interior (Set.Ici βc)) := by
    rw [hint]
    intro x hx
    exact ((hd x hx).differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici βc), c0 ≤ deriv M x := by
    intro x hx
    rw [hint] at hx
    rw [(hd x hx).deriv]
    exact hge x hx
  have h := (convex_Ici βc).mul_sub_le_image_sub_of_le_deriv hc hdiff hderiv βc
    Set.self_mem_Ici β (Set.mem_Ici.mpr hβ) hβ
  rwa [hM0, sub_zero] at h

/-! ## Sharpness of the phase transition -/

open Ising in
/-- **Sharpness of the phase transition for the Ising model** (Aizenman–Barsky,
Duminil-Copin–Tassion), in the form of a Lean-checked reduction.

For a finite-volume Ising model with couplings `J`, origin `o` and a distance
function `d`, `twoPoint β J o d n` is the largest correlation `⟨σ_o σ_v⟩` over the
vertices `v` at distance `n` from `o`, and `M` is the magnetization, with critical
point `βc`.

Assuming the two standard analytic inputs of the Duminil-Copin–Tassion argument:

* (subcritical) below `βc` the two-point function contracts by a factor `c < 1`
  over some fixed scale `L`, and it is nonnegative (Griffiths' inequality);
* (supercritical) above `βc` the magnetization is differentiable with derivative
  bounded below by `c₀`, is continuous up to `βc` and vanishes at `βc`;

the phase transition is *sharp*:

* for every `β < βc` the two-point function decays exponentially in the distance;
* for every `β ≥ βc` the magnetization satisfies the mean-field lower bound
  `M β ≥ c₀ (β - βc)`.

The third conclusion is the infinite-temperature base case, which is proved
unconditionally: at `β = 0` all correlations between distinct sites vanish. -/
