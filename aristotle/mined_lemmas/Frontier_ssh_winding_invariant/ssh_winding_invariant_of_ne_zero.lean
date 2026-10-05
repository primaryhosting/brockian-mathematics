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

theorem ssh_winding_invariant_of_ne_zero (v w : ℝ) (hw : w ≠ 0) (hgap : |v| ≠ |w|) :
    sshWinding v w = ((if |v| < |w| then (1 : ℤ) else 0 : ℤ) : ℂ) := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have habs : |w| = -w := abs_of_neg hneg
    have hpos' : 0 < -w := neg_pos.2 hneg
    have hmain := ssh_winding_invariant v (-w) hpos' (by rwa [← habs])
    have hswap : sshWinding v w = sshWinding v (-w) := by
      simpa using sshWinding_neg v (-w)
    rw [hswap, hmain, habs]
  · have habs : |w| = w := abs_of_pos hpos
    rw [habs]
    exact ssh_winding_invariant v w hpos (by rwa [← habs])

end Frontier

