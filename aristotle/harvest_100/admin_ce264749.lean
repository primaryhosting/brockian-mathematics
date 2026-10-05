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

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionUniformity

open scoped BigOperators

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]

omit [Fintype G] [Fintype X] in
/-- A function invariant under a transitive symmetry group is constant. -/
theorem eq_of_invariant [MulAction.IsPretransitive G X]
    {w : X → ℝ} (hw : ∀ (g : G) (y : X), w (g • y) = w y) (x y : X) : w y = w x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  rw [← hg, hw]

omit [Fintype G] in
/-- A function invariant under a transitive symmetry group equals its own average:
it is *equidistributed* over the underlying set. -/
theorem invariant_eq_average [MulAction.IsPretransitive G X]
    {w : X → ℝ} (hw : ∀ (g : G) (y : X), w (g • y) = w y) (x : X) :
    w x = (∑ y : X, w y) / Fintype.card X := by
  have hcard : (0 : ℝ) < Fintype.card X := by
    have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  have hsum : (∑ y : X, w y) = Fintype.card X * w x := by
    rw [Finset.sum_congr rfl (fun y _ => eq_of_invariant (G := G) hw x y)]
    simp [Finset.sum_const, mul_comm]
  rw [hsum]
  field_simp

/-- The group-average of `f` along the orbit of a point has the same total mass as `f`. -/
theorem sum_orbit_average (f : X → ℝ) :
    (∑ x : X, ∑ g : G, f (g • x)) = Fintype.card G * ∑ x : X, f x := by
  rw [Finset.sum_comm]
  have : ∀ g : G, (∑ x : X, f (g • x)) = ∑ x : X, f x := by
    intro g
    exact Fintype.sum_bijective (fun x => g • x) (MulAction.bijective g) _ _ (fun _ => rfl)
  simp [this, Finset.sum_const, mul_comm]

/-- **Equidistribution of transitive symmetry.**  If a finite group `G` acts transitively on a
finite set `X`, then for every real-valued function `f` on `X` and every point `x`, the average
of `f` over the group orbit of `x` (counted with multiplicity over `G`) equals the average of
`f` over all of `X`.  Equivalently, the orbit of any point is equidistributed in `X`. -/
theorem equidistribution_of_transitive_symmetry [MulAction.IsPretransitive G X]
    (f : X → ℝ) (x : X) :
    (∑ g : G, f (g • x)) / Fintype.card G = (∑ y : X, f y) / Fintype.card X := by
  set w : X → ℝ := fun y => (∑ g : G, f (g • y)) / Fintype.card G with hwdef
  have hw : ∀ (g : G) (y : X), w (g • y) = w y := by
    intro g y
    have hre : (∑ h : G, f (h • (g • y))) = ∑ h : G, f (h • y) := by
      refine Fintype.sum_bijective (fun h => h * g) (Group.mulRight_bijective g) _ _ ?_
      intro h
      simp [mul_smul]
    simp [hwdef, hre]
  have hmain := invariant_eq_average (G := G) hw x
  have hcardG : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
    positivity
  have hsumw : (∑ y : X, w y) = (∑ y : X, f y) := by
    have h1 : (∑ y : X, w y) = (∑ y : X, ∑ g : G, f (g • y)) / Fintype.card G := by
      simp [hwdef, Finset.sum_div]
    rw [h1, sum_orbit_average (G := G) f]
    field_simp
  rw [hsumw] at hmain
  simpa [hwdef] using hmain

#print axioms equidistribution_of_transitive_symmetry

end Brockian.EquidistributionUniformity

