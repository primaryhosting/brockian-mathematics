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

theorem sshWinding_topological (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball ((v : ℂ)) w := by
    simp only [Metric.mem_ball, dist_zero_left]
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hcirc : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball hmem
    simpa using this
  rw [sshWinding_eq_circleIntegral, hcirc]
  have hpi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- In the trivial phase `w < |v|` the winding number equals `0`. -/
