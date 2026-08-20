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

import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Complex Metric

/-- The (analytically continued) off-diagonal entry of the SSH Bloch Hamiltonian.
With `z = exp (I * k)` on the unit circle, `sshBloch v w z = v + w * z` is the
intra-cell/inter-cell hopping combination `v + w * e^{i k}`. -/

lemma two_pi_I_ne_zero : (2 * Real.pi * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]

/-- Key intermediate lemma (topological case): when the inter-cell hopping dominates,
the integrand is the Cauchy kernel of a pole inside the unit disk. -/
