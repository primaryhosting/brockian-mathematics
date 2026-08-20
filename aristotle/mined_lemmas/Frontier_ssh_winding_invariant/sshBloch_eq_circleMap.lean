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

set_option grind.warning false

namespace Frontier

open Complex Metric

/-- The off-diagonal (inter-sublattice) component of the Bloch Hamiltonian of the
Su–Schrieffer–Heeger (SSH) chain with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w * exp (i k)`.  The full Bloch Hamiltonian is the chiral (off-diagonal) matrix
`[[0, h k], [conj (h k), 0]]`, so its spectral gap is open exactly when `h k ≠ 0` for all `k`. -/

lemma sshBloch_eq_circleMap (v w : ℝ) : sshBloch v w = circleMap (v : ℂ) w := rfl

/-- The winding number is `(2πi)⁻¹` times the contour integral of `1/z` over that circle. -/
