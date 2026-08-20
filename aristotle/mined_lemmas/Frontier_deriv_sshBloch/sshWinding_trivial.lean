/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is the chiral (off-diagonal) matrix
`[[0, h(k)], [conj (h k), 0]]`, so the spectral gap is open at `k` iff `h k ≠ 0`. -/

theorem sshWinding_trivial (v w : ℝ) (hw : 0 < w) (h : w < |v|) : sshWinding v w = 0 := by
  have hnot : ∀ z ∈ Metric.closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [Metric.mem_closedBall] at hz
    rw [hz0] at hz
    rw [dist_zero_left] at hz
    simp only [Complex.norm_real, Real.norm_eq_abs] at hz
    linarith
  have hcirc : (∮ z in C((v : ℂ), w), z⁻¹) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hw.le
      Set.countable_empty ?_ ?_
    · exact ContinuousOn.inv₀ continuousOn_id (fun z hz => hnot z hz)
    · intro z hz
      exact differentiableAt_inv (hnot z (Metric.ball_subset_closedBall hz.1))
  rw [sshWinding_eq_circleIntegral, hcirc, mul_zero]

/-- **SSH winding invariant.**  For a gapped SSH chain (`w > 0`, `|v| ≠ w`), the Bloch
Hamiltonian is nowhere degenerate, and the winding number
`W = (2π i)⁻¹ ∫_0^{2π} h'(k)/h(k) dk` of the Bloch loop `h(k) = v + w e^{ik}` is an
*integer*: it equals `1` in the topological phase `|v| < w` and `0` in the trivial phase
`|v| > w`.  Thus the topological phase of the SSH model is classified by a `ℤ`-valued
winding number, which is locally constant (constant on each of the two gapped phases). -/
