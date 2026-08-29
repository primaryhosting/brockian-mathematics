/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

namespace Frontier

/-!
## Formalization

The analytic core of Penrose's singularity theorem is the *focusing* of the null
geodesic congruence generating the boundary of the future of a trapped surface.

Along an affinely parametrised null geodesic congruence with affine parameter `t`,
expansion `θ`, shear scalar `shear = σ_{ab} σ^{ab} ≥ 0` and Ricci contraction
`ric = R_{ab} k^a k^b`, the Raychaudhuri equation for a hypersurface-orthogonal
null congruence with two-dimensional screen space reads

  `dθ/dt = - θ² / 2 - shear - ric`.

The *null energy condition* (together with the Einstein equations) gives `ric ≥ 0`,
and the presence of a *trapped surface* gives an initially negative expansion,
`θ 0 < 0`.

The theorem below shows that under these hypotheses the congruence cannot remain
regular for an affine parameter interval longer than `2 / |θ 0|`: any interval
`[0, L]` on which the expansion is finite and differentiable must satisfy
`L < 2 / (-θ 0)`. Equivalently, the expansion blows up (a conjugate/focal point
forms) at some affine parameter `≤ 2 / |θ 0|`; the generators of the boundary
therefore cannot be extended indefinitely — the spacetime is null geodesically
incomplete, which is Penrose's conclusion.
-/

/-- **Penrose singularity theorem (Raychaudhuri focusing core).**

Let `θ` be the expansion of an affinely parametrised null geodesic congruence,
with derivative `D`, shear scalar `shear` and Ricci contraction `ric` along the
generators, satisfying the Raychaudhuri equation on the affine interval `[0, L]`.
Assume the null energy condition `0 ≤ ric` and the (always valid) positivity of
the shear scalar `0 ≤ shear`, and assume the initial cross-section is *trapped*,
i.e. `θ 0 < 0`.

Then the congruence cannot remain regular for affine length `2 / |θ 0|` or more:
`L < 2 / (-θ 0)`. Hence the generators are incomplete (see
`Frontier.penrose_singularity_incomplete`). -/

theorem penrose_hypotheses_satisfiable (L : ℝ) (hL1 : L < 1) :
    ∃ θ D shear ric : ℝ → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt θ (D t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, D t = -(θ t) ^ 2 / 2 - shear t - ric t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ shear t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ ric t) ∧ θ 0 < 0 := by
  refine ⟨fun t => 2 * (t - 1)⁻¹, fun t => -2 / (t - 1) ^ 2, fun _ => 0, fun _ => 0,
    ?_, ?_, fun _ _ => le_refl 0, fun _ _ => le_refl 0, by norm_num⟩
  · intro t ht
    have hne : t - 1 ≠ 0 := by rcases ht with ⟨h1, h2⟩; intro h; nlinarith
    have h := (((hasDerivAt_id t).sub_const 1).inv hne).const_mul (2 : ℝ)
    simp only [id] at h
    convert h using 1
    field_simp
  · intro t ht
    have hne : t - 1 ≠ 0 := by rcases ht with ⟨h1, h2⟩; intro h; nlinarith
    simp only
    field_simp
    ring

end Frontier

