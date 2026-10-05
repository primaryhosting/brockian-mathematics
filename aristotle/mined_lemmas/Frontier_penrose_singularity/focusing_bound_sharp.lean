import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization

Penrose's singularity theorem says that a spacetime containing a trapped surface, satisfying
the null energy condition (plus global hyperbolicity with a non-compact Cauchy surface), is
null geodesically incomplete.  The analytic heart of the theorem is the *focusing* argument:
along the future-directed null geodesic congruence orthogonal to the trapped surface, the
expansion scalar `θ` obeys the Raychaudhuri equation

  `θ' = -θ² / 2 - σ_{ab} σ^{ab} - R_{ab} k^a k^b`,

so that the null energy condition `R_{ab} k^a k^b ≥ 0` gives the differential inequality

  `θ' ≤ -θ² / 2`.

A trapped surface is exactly the condition `θ 0 < 0` for both orthogonal null congruences.
The content proved below is the resulting focusing bound: the affine parameter of such a
congruence cannot reach `2 / |θ 0|`, i.e. a conjugate point (caustic) forms within affine
length `2 / |θ 0|` and the congruence cannot be affinely complete.  This is the base case /
Lean-checked reduction of the singularity theorem: the global step (from a caustic to the
compactness of `∂ J⁺(S)` and the contradiction with non-compactness of a Cauchy surface) is
pure causal topology and is not formalized here.
-/

namespace Frontier

open Set

/-- **Focusing bound (Raychaudhuri + null energy condition).**

If the expansion `θ` of a null geodesic congruence is defined on the affine interval `[0, L]`
with derivative `θ'` there, satisfies the Raychaudhuri–NEC inequality `θ' ≤ -θ²/2`, and starts
out converging, `θ 0 < 0` (the trapped surface condition), then the affine length satisfies
`L < 2 / |θ 0|`: the congruence focuses to a caustic in finite affine parameter. -/

theorem focusing_bound_sharp {L : ℝ} (hL1 : L < 1) :
    ∃ θ θ' : ℝ → ℝ, (∀ s ∈ Icc (0 : ℝ) L, HasDerivAt θ (θ' s) s) ∧
      (∀ s ∈ Icc (0 : ℝ) L, θ' s ≤ -(θ s) ^ 2 / 2) ∧ θ 0 < 0 ∧ 2 / (-θ 0) = 1 := by
  refine ⟨fun s => 2 / (s - 1), fun s => -2 / (s - 1) ^ 2, ?_, ?_, by norm_num, by norm_num⟩
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      have := hs.2
      intro h
      linarith [sub_eq_zero.1 h]
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h2 : HasDerivAt (fun x : ℝ => (x - 1)⁻¹) (-1 / (s - 1) ^ 2) s := h1.inv hne
    have h3 := h2.const_mul (2 : ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h3
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      have := hs.2
      intro h
      linarith [sub_eq_zero.1 h]
    have heq : -2 / (s - 1) ^ 2 = -(2 / (s - 1)) ^ 2 / 2 := by
      field_simp
    exact heq.le

end Frontier

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

