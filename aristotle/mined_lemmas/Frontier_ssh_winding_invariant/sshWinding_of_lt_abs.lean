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

open Complex Metric intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
model with intracell hopping `v` and intercell hopping `w`:
`h v w k = v + w * exp (i k)`.  Chiral symmetry forces the Bloch Hamiltonian to have the
form `![![0, h k], ![conj (h k), 0]]`, so the spectral gap is open exactly when `h k ≠ 0`
for all `k`. -/

lemma sshWinding_of_lt_abs (v w : ℝ) (hw : 0 ≤ w) (h : w < |v|) : sshWinding v w = 0 := by
  have hne : ∀ z ∈ Metric.closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [Metric.mem_closedBall, Complex.dist_eq, hz0] at hz
    simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz
    linarith
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (closure (Metric.ball ((v : ℂ)) w)) := by
    intro z hz
    exact (differentiableAt_inv (hne z (closure_ball_subset_closedBall hz))).differentiableWithinAt
  have hzero : (∮ z in C((v : ℂ), w), z⁻¹) = 0 :=
    DiffContOnCl.circleIntegral_eq_zero hw hdiff.diffContOnCl
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- The winding integrand `h'(k) / h(k)` is `2π`-periodic in the quasimomentum. -/
