import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

set_option grind.warning false

namespace Frontier

/-!
## Formalization

Penrose's singularity theorem states that a spacetime containing a *trapped surface*,
satisfying the *null energy condition* (together with the genericity/global hypotheses),
cannot be null geodesically complete.

Mathlib does not (yet) contain Lorentzian causal theory, so we formalize the analytic
engine of the theorem, which is where the physics enters and which is a Lean-checked
reduction of the full statement:

* Let `θ : ℝ → ℝ` be the *expansion* of the congruence of null geodesics emanating
  orthogonally from a closed surface, as a function of the affine parameter `t`.
* The **Raychaudhuri equation** for a hypersurface-orthogonal null congruence reads
  `dθ/dt = -θ²/2 - σ_{ab}σ^{ab} - Ric(k,k)`.
  The null energy condition gives `Ric(k,k) ≥ 0`, and the shear term satisfies
  `σ_{ab}σ^{ab} ≥ 0`, so the physical input is exactly the differential inequality
  `deriv θ t ≤ -(θ t)^2 / 2`   (hypothesis `hray` below).
* The surface being **trapped** means the expansion is initially negative:
  `θ 0 < 0`   (hypothesis `htrapped` below).

`Frontier.focusing_length_bound` then shows that the congruence can only remain smooth
(i.e. free of a focal point / caustic) for affine parameter `t < 2/|θ 0|`, and
`Frontier.penrose_singularity` concludes that no such congruence can be complete,
i.e. defined and smooth for all affine parameters `t ≥ 0`: geodesic incompleteness.
-/

/-- Under the Raychaudhuri inequality the expansion is non-increasing: in particular a
congruence that is initially converging (trapped) stays converging. -/

theorem expansion_antitone {L : ℝ} {θ : ℝ → ℝ}
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ θ t)
    (hray : ∀ t ∈ Set.Icc (0 : ℝ) L, deriv θ t ≤ -(θ t) ^ 2 / 2) :
    AntitoneOn θ (Set.Icc (0 : ℝ) L) := by
  have hcont : ContinuousOn θ (Set.Icc (0 : ℝ) L) := fun t ht =>
    (hdiff t ht).continuousAt.continuousWithinAt
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hdiff x (Set.mem_Icc_of_Ioo hx)).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h := hray x (Set.mem_Icc_of_Ioo hx)
    nlinarith [sq_nonneg (θ x)]

/-- The expansion of a trapped congruence stays strictly negative on its domain. -/
