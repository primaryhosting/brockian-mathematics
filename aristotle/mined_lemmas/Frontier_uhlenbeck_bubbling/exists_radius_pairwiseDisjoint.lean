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

theorem exists_radius_pairwiseDisjoint {X : Type*} [MetricSpace X] (s : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑s : Set X).PairwiseDisjoint (fun x : X => Metric.ball x r) := by
  classical
  set D : Finset ℝ := s.offDiag.image (fun p : X × X => dist p.1 p.2) with hD
  by_cases hne : D.Nonempty
  · refine ⟨D.min' hne / 2, ?_, ?_⟩
    · obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp (D.min'_mem hne)
      rw [Finset.mem_offDiag] at hp
      have hpos : 0 < dist p.1 p.2 := dist_pos.2 hp.2.2
      rw [hpd] at hpos
      linarith
    · intro x hx y hy hxy
      have hdxy : D.min' hne ≤ dist x y := by
        apply Finset.min'_le
        rw [hD, Finset.mem_image]
        exact ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro z hz hz'
      rw [Metric.mem_ball, dist_comm] at hz hz'
      have htri := dist_triangle x z y
      rw [dist_comm z y] at htri
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    exfalso
    refine hne ⟨dist x y, ?_⟩
    rw [hD, Finset.mem_image]
    exact ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩

/-! ## The bubbling set of a limiting energy measure -/

/-- The **bubbling (concentration) set** of a measure `μ` at energy threshold `ε₀`:
the points at which every ball carries at least `ε₀` of the energy.  For the limit of a
sequence of Yang–Mills connections these are exactly the points where a bubble can form. -/
