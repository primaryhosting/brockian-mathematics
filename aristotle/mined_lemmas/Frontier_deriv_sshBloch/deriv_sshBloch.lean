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

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is the chiral (off-diagonal) matrix
`[[0, h(k)], [conj (h k), 0]]`, so the spectral gap is open at `k` iff `h k ≠ 0`. -/

theorem deriv_sshBloch (v w : ℝ) (k : ℝ) :
    deriv (fun t : ℝ => sshBloch v w t) k
      = Complex.I * (w : ℂ) * Complex.exp (Complex.I * (k : ℂ)) := by
  have h : (fun t : ℝ => sshBloch v w t)
      = fun t : ℝ => (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * (t : ℝ)) := rfl
  rw [h]
  have hd : HasDerivAt (fun t : ℝ => (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * (t : ℝ)))
      (Complex.I * (w : ℂ) * Complex.exp (Complex.I * (k : ℂ))) k := by
    have h1 : HasDerivAt (fun t : ℝ => (Complex.I * (t : ℂ))) Complex.I k := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := k)).const_mul Complex.I
    have h2 := (h1.cexp).const_mul (w : ℂ)
    have h3 := h2.const_add ((v : ℂ))
    convert h3 using 1
    ring
  exact hd.deriv

/-- The gap of the SSH chain is open at every quasi-momentum iff `|v| ≠ w` (for `w > 0`). -/
