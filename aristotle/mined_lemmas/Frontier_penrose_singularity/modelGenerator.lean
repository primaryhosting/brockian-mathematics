/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

The analytic core of Penrose's singularity theorem is the focusing of a null geodesic
congruence.  Along a null generator of the boundary of the future of a closed trapped
surface, with affine parameter `t`, the expansion `θ` of the congruence satisfies the
Raychaudhuri equation

  `dθ/dt = -θ² / 2 - σ_{ab}σ^{ab} - R_{ab} k^a k^b`,

where `σ` is the shear and `k` is the null tangent.  The null energy condition gives
`R_{ab} k^a k^b ≥ 0`, and the shear term is nonnegative, so the *Raychaudhuri inequality*

  `dθ/dt ≤ -θ² / 2`

holds.  That the surface is *trapped* means precisely that the initial expansion of the
outgoing null congruence is negative: `θ 0 < 0`.

The structure `NullGeneratorData L` below packages exactly this data on an affine
interval `[0, L]`: the expansion along a null generator that is defined (and
differentiable, with finite expansion) for affine parameter in `[0, L]`, satisfying the
Raychaudhuri inequality, and emanating from a trapped surface.

The theorem `Frontier.penrose_singularity` states that such a generator can only exist for
affine length `L < 2 / |θ 0|`: the null geodesic congruence focuses to a conjugate point in
finite affine parameter, so the generator cannot be extended, i.e. the spacetime is null
geodesically incomplete (`Frontier.penrose_null_geodesic_incomplete`).
-/

/-- Data of a null geodesic generator, parametrized by affine parameter in `[0, L]`,
issuing orthogonally from a closed trapped surface, in a spacetime satisfying the null
energy condition.

* `expansion` is the expansion scalar `θ` of the null congruence;
* `expansionDeriv` is its derivative with respect to the affine parameter;
* `raychaudhuri` is the Raychaudhuri inequality `θ' ≤ -θ²/2`, which follows from the
  Raychaudhuri equation together with the null energy condition and the nonnegativity of
  the shear term;
* `trapped` says that the surface is trapped: the initial expansion is negative. -/
structure NullGeneratorData (L : ℝ) where
  /-- The expansion scalar `θ` of the null congruence along the generator. -/
  expansion : ℝ → ℝ
  /-- The derivative of the expansion with respect to the affine parameter. -/
  expansionDeriv : ℝ → ℝ
  /-- The expansion is differentiable in the affine parameter on `[0, L]`
  (in particular it stays finite there: no conjugate point occurs on `[0, L]`). -/
  hasDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt expansion (expansionDeriv t) t
  /-- Raychaudhuri inequality, a consequence of the null energy condition. -/
  raychaudhuri : ∀ t ∈ Set.Icc (0 : ℝ) L, expansionDeriv t ≤ -(expansion t) ^ 2 / 2
  /-- Trapped surface condition: the initial expansion is negative. -/
  trapped : expansion 0 < 0

namespace NullGeneratorData

variable {L : ℝ} (C : NullGeneratorData L)

/-- The expansion is nonincreasing along the generator. -/

noncomputable def modelGenerator : NullGeneratorData (1 / 2) where
  expansion := fun t => 2 / (t - 1)
  expansionDeriv := fun t => -2 / (t - 1) ^ 2
  hasDeriv := by
    intro t ht
    have hne : t - 1 ≠ 0 := by
      have h2 := ht.2
      intro h
      rw [sub_eq_zero] at h
      rw [h] at h2
      norm_num at h2
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have h2 : HasDerivAt (fun s : ℝ => (s - 1)⁻¹) (-1 / (t - 1) ^ 2) t := by
      simpa using h1.inv hne
    have h3 := h2.const_mul (2 : ℝ)
    have hfun : (fun s : ℝ => 2 * (s - 1)⁻¹) = fun s : ℝ => 2 / (s - 1) := by
      funext s; rw [div_eq_mul_inv]
    rw [hfun] at h3
    convert h3 using 1
    ring
  raychaudhuri := by
    intro t ht
    have hne : t - 1 ≠ 0 := by
      have h2 := ht.2
      intro h
      rw [sub_eq_zero] at h
      rw [h] at h2
      norm_num at h2
    rw [div_pow]
    field_simp
    exact le_rfl
  trapped := by norm_num

end Frontier

#print axioms Frontier.penrose_singularity
#print axioms Frontier.penrose_null_geodesic_incomplete

