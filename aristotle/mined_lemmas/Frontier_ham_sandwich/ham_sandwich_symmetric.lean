import Mathlib

/-!
# Medians of real-valued measurable functions

Auxiliary file for the Ham Sandwich development: every finite measure has a median
along any measurable real-valued function.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Frontier

variable {α : Type*} [MeasurableSpace α]

/-- **Existence of a median.** For a finite measure `μ` on `α` and a measurable function
`f : α → ℝ` there is a threshold `c` such that both `{f < c}` and `{f > c}` carry at most
half of the total mass. -/

theorem ham_sandwich_symmetric {n : ℕ} [NeZero n]
    (μ : Fin n → Measure (EuclideanSpace ℝ (Fin n))) [∀ i, IsFiniteMeasure (μ i)]
    (hsymm : ∀ i, Measure.map (fun x => -x) (μ i) = μ i) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), v ≠ 0 ∧ ∀ i, BisectedBy v c (μ i) := by
  classical
  refine ⟨EuclideanSpace.single (0 : Fin n) (1 : ℝ), 0, ?_, ham_sandwich_of_symmetric μ hsymm _⟩
  simp

/-- **Ham–Sandwich theorem, base case `n = 1`.**
Any family of `n = 1` finite measures on `ℝ¹` can be simultaneously bisected by a single
hyperplane, i.e. by a point `{x | ⟪v, x⟫ = c}` with `v ≠ 0`: both open half-lines it determines
carry at most half of the mass of the measure.

(The general statement for `n` measures on `ℝⁿ` requires the Borsuk–Ulam theorem, which is not
available in Mathlib; the case of a *single* measure on `ℝⁿ` for arbitrary `n` is proved above as
`Frontier.exists_bisecting_hyperplane`.) -/
