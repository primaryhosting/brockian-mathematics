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

theorem add_liminf_le_liminf_add (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n : ℕ => u n + v n) atTop := by
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat]
  have hmonoU : Monotone (fun n : ℕ => ⨅ i ≥ n, u i) := fun a b hab =>
    le_iInf₂ fun i hi => iInf₂_le i (le_trans hab hi)
  have hmonoV : Monotone (fun n : ℕ => ⨅ i ≥ n, v i) := fun a b hab =>
    le_iInf₂ fun i hi => iInf₂_le i (le_trans hab hi)
  rw [ENNReal.iSup_add_iSup (fun i j => ⟨max i j,
    add_le_add (hmonoU (le_max_left i j)) (hmonoV (le_max_right i j))⟩)]
  exact iSup_mono fun n => le_iInf₂ fun i hi => add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- Superadditivity of `liminf` for a finite family of `ℝ≥0∞`-valued sequences. -/
