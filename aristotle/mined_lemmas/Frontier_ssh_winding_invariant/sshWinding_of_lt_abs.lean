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

open Complex Metric

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is `H(k) = Re h(k) • σₓ + Im h(k) • σ_y`,
so the spectral gap is open exactly when `h(k) ≠ 0` for all `k`. -/

theorem sshWinding_of_lt_abs (v w : ℝ) (hw : 0 ≤ w) (h : w < |v|) : sshWinding v w = 0 := by
  have hne : ∀ z ∈ closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [mem_closedBall, dist_eq, hz0] at hz
    have : |v| ≤ w := by simpa using hz
    exact absurd h (not_lt.mpr this)
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) (closedBall ((v : ℂ)) w) :=
    fun z hz => (continuousAt_inv₀ (hne z hz)).continuousWithinAt
  have hzero : (∮ z in C((v : ℂ), w), z⁻¹) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hw
      (Set.countable_empty) hcont
      (fun z hz => differentiableAt_inv_iff.mpr (hne z (ball_subset_closedBall hz.1)))
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- **The SSH topological invariant.**  For `|v| ≠ w` (an open gap) the winding number of the
Bloch loop `k ↦ v + w e^{ik}` around the origin is an integer, equal to `1` in the topological
phase `|v| < w` and to `0` in the trivial phase `w < |v|`. -/
