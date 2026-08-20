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

/-!
# The Ham–Sandwich theorem

The Ham–Sandwich theorem states that any `n` finite measures on `ℝⁿ` can be simultaneously
bisected by a single affine hyperplane.  Here a hyperplane is described by a nonzero normal
vector `v` and a level `c`, and "bisecting" a measure `μ` means that each of the two closed
half-spaces `{x | ⟪v, x⟫ ≤ c}` and `{x | c ≤ ⟪v, x⟫}` carries at least half of the total mass
of `μ`.

The general statement is recorded as `Frontier.HamSandwich n`.  The full theorem for arbitrary
`n` rests on the Borsuk–Ulam theorem, which is not available in Mathlib.  We prove here the base
case `n = 1` (`Frontier.ham_sandwich`), together with a genuinely more general statement
(`Frontier.bisect_one_measure`): a *single* finite measure on `ℝⁿ` can be bisected by a
hyperplane with any prescribed normal direction.  Both rest on the existence of a median of a
real random variable (`Frontier.exists_median`).
-/

namespace Frontier

open MeasureTheory Filter Set Topology

/-- A hyperplane with normal vector `v` and level `c` bisects the measure `μ` if each of the two
closed half-spaces it bounds carries at least half of the total mass of `μ`. -/

theorem ham_sandwich : HamSandwich 1 := by
  intro μ hμ
  refine ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_, ?_⟩
  · intro h
    have := congrFun (congrArg (fun y : EuclideanSpace ℝ (Fin 1) => (y : Fin 1 → ℝ)) h) 0
    simp [EuclideanSpace.single_apply] at this
  · haveI := hμ 0
    obtain ⟨c, hc⟩ := bisect_one_measure (μ 0) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    exact ⟨c, fun i => by simpa [Subsingleton.elim i 0] using hc⟩

end Frontier

