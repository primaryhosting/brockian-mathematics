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

lemma sshWinding_of_abs_lt (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball ((v : ℂ)) w := by
    simpa [Complex.dist_eq, Complex.norm_real] using h
  have hint : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball hmem
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]
  rw [sshWinding_eq_circleIntegral, hint, inv_mul_cancel₀ hne]

/-- Trivial phase: if `w < |v|` the origin lies outside the circle and the winding
number is `0`. -/
