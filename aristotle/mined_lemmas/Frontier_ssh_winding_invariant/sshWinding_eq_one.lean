/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
chain with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The two-band Hamiltonian is
`H(k) = [[0, h(k)], [conj (h k), 0]]`, whose spectral gap is open iff `h k ≠ 0`. -/

theorem sshWinding_eq_one (v w : ℝ) (hw : 0 < w) (hvw : |v| < w) :
    sshWinding v w = 1 := by
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hmem : (-(v / w) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    have : ‖(-(v / w) : ℂ)‖ < 1 := by
      have : ‖(-(v / w) : ℂ)‖ = |v| / w := by
        rw [norm_neg]
        rw [show ((v : ℂ) / (w : ℂ)) = ((v / w : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hw]
      rw [this]
      exact (div_lt_one hw).2 hvw
    simpa [Metric.mem_ball, dist_eq_norm] using this
  have hfun : ∀ z : ℂ, (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) = (z - (-(v / w) : ℂ))⁻¹ := by
    intro z
    rw [sub_neg_eq_add]
    rw [eq_comm, inv_eq_iff_eq_inv, eq_comm, inv_div]
    field_simp
    ring
  rw [sshWinding_eq_circleIntegral]
  simp only [hfun]
  rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
  field_simp

/-- In the trivial phase `w < |v|` the SSH winding number equals `0`. -/
