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

theorem sshWinding_of_abs_lt (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball ((v : ℂ)) w := by
    simp only [mem_ball, dist_eq, zero_sub, norm_neg]
    simpa using h
  have := circleIntegral.integral_sub_inv_of_mem_ball hmem
  simp only [sub_zero] at this
  rw [sshWinding_eq_circleIntegral, this]
  field_simp

/-- **Trivial phase** (`w < |v|`): the SSH winding number equals `0`. -/
