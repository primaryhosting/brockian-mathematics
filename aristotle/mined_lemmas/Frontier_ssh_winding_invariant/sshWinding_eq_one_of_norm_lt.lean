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

theorem sshWinding_eq_one_of_norm_lt (v w : ℂ) (h : ‖v‖ < ‖w‖) :
    sshWinding v w = 1 := by
  have hw : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at h
    exact absurd h (not_lt.2 (norm_nonneg v))
  have hcong : ∀ z : ℂ, w / (v + w * z) = (z - (-v / w))⁻¹ := by
    intro z
    have hz : z - (-v / w) = (v + w * z) / w := by
      field_simp
      ring
    rw [hz, inv_div]
  have hmem : (-v / w) ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_div, norm_neg]
    rw [div_lt_one (by positivity)]
    exact h
  have : ∮ z in C(0, 1), w / (v + w * z) = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [circleIntegral.integral_congr zero_le_one (fun z _ => hcong z)]
    exact circleIntegral.integral_sub_inv_of_mem_ball hmem
  rw [sshWinding_eq_circleIntegral, this, inv_mul_cancel₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The winding number only depends on the SSH Bloch function up to a nonzero overall
rescaling of the two hopping amplitudes (the log-derivative integrand is scale invariant). -/
