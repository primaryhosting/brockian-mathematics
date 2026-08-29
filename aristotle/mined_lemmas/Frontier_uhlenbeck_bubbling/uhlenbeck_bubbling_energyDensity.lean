import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal
open scoped Topology

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

open MeasureTheory Metric Set Filter

namespace Frontier

/-!
## Setting

For a sequence of Yang–Mills connections `A i` on a bundle over a Riemannian manifold `X`
with uniformly bounded energy, the energy densities `|F_{A i}|² dvol` form a sequence of
Borel measures on `X` with uniformly bounded total mass.  Uhlenbeck's theory says:

* (ε-regularity)  there is an energy quantum `ε₀ > 0` such that if the energy in some ball
  around `x` is `< ε₀`, then the convergence is smooth up to gauge near `x` and the
  singularity there is removable;
* (bubbling)  consequently the set of points at which the convergence fails is contained in
  the *concentration set*, which is a finite set with at most `(total energy)/ε₀` points:
  energy concentrates ("bubbles off") at finitely many points only.

The development below formalizes and proves the measure-theoretic core of this picture, in
two forms.

* `Frontier.uhlenbeck_bubbling`: for the limiting energy measure `μ` (of finite total
  energy) and a positive energy quantum `ε₀`, the bubbling set is closed and finite, the
  number of bubble points satisfies `#(bubble points) · ε₀ ≤ total energy`, and — given
  ε-regularity as a hypothesis — every point off the bubbling set is a regular point.
  This is exactly the reduction of Uhlenbeck bubbling to the local ε-regularity theorem.

* `Frontier.uhlenbeck_bubbling_sequence`: the same conclusions directly along a *sequence*
  of energy measures with uniformly bounded total energy `E`, where the bubbling set is
  defined through the lower limit of the energy in small balls; no weak limit of measures
  needs to be extracted.  (The lower limit is the correct notion here: with the upper limit
  the statement is false, since energy may oscillate between two points along a sequence.)

The two remaining analytic inputs of Uhlenbeck's theorem — the local ε-regularity /
removable singularity theorem and Uhlenbeck's gauge fixing — enter as the hypothesis `hreg`.
-/

/-! ## Auxiliary arithmetic and disjointness lemmas -/

/-- For a finite bound `E` and a positive quantum `ε₀`, some multiple `n • ε₀` exceeds `E`. -/

theorem uhlenbeck_bubbling_energyDensity {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfin : ∫⁻ x : EuclideanSpace ℝ (Fin d), f x ≠ ⊤) {ε₀ : ℝ≥0∞}
    (hε₀ : 0 < ε₀) :
    IsClosed (bubbleSet (volume.withDensity f) ε₀) ∧
      (bubbleSet (volume.withDensity f) ε₀).Finite ∧
      ((bubbleSet (volume.withDensity f) ε₀).ncard : ℝ≥0∞) * ε₀
        ≤ ∫⁻ x : EuclideanSpace ℝ (Fin d), f x := by
  have hmass : (volume.withDensity f) Set.univ = ∫⁻ x : EuclideanSpace ℝ (Fin d), f x := by
    rw [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]
  have : IsFiniteMeasure (volume.withDensity f) :=
    ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hfin⟩
  refine ⟨bubbleSet_isClosed _ ε₀, bubbleSet_finite _ hε₀, ?_⟩
  rw [← hmass]
  exact bubbleSet_ncard_mul_le _ hε₀

end Frontier

