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

lemma sshBloch_deriv (v w : ℂ) : deriv (sshBloch v w) = fun _ => w := by
  funext z
  have h0 : HasDerivAt (fun x : ℂ => v + w * x) (w * 1) z :=
    ((hasDerivAt_id z).const_mul w).const_add v
  rw [mul_one] at h0
  exact h0.deriv

