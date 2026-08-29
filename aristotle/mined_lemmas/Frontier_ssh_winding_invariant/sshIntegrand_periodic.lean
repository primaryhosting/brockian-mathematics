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

lemma sshIntegrand_periodic (v w : ℝ) :
    Function.Periodic
      (fun k : ℝ => (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k)
      (2 * Real.pi) := by
  intro k
  have hexp : Complex.exp (((k + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((k : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [sshOffDiag, hexp]

/-- Reversing the sign of the intercell hopping `w` amounts to the shift `k ↦ k + π`
of the quasimomentum, so it leaves the winding number unchanged. -/
