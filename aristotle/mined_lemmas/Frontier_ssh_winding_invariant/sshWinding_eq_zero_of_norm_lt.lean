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

/-- Off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger) chain,
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`. Chiral symmetry makes the Bloch Hamiltonian
`[[0, h(k)], [conj h(k), 0]]`, so the topology is entirely carried by `h`. -/

theorem sshWinding_eq_zero_of_norm_lt (v w : ℂ) (h : ‖w‖ < ‖v‖) :
    sshWinding v w = 0 := by
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → v + w * z ≠ 0 := by
    intro z hz hzero
    have : ‖w * z‖ ≤ ‖w‖ := by
      rw [norm_mul]
      calc ‖w‖ * ‖z‖ ≤ ‖w‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hz (norm_nonneg w)
        _ = ‖w‖ := mul_one _
    have hv : v = -(w * z) := by linear_combination hzero
    rw [hv, norm_neg] at h
    exact absurd h (not_lt.2 this)
  have hzero : ∮ z in C(0, 1), w / (v + w * z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one
      Set.countable_empty ?_ ?_
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
      intro z hz
      exact hne z (by simpa [Complex.dist_eq] using hz)
    · intro z hz
      have hz' : ‖z‖ ≤ 1 := le_of_lt (by simpa [Complex.dist_eq] using hz.1)
      exact ((differentiableAt_const w).div
        ((differentiableAt_const v).add ((differentiableAt_const w).mul differentiableAt_id))
        (hne z hz'))
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- Topological phase: if the intercell hopping dominates (`‖v‖ < ‖w‖`),
the winding number is `1`. -/
