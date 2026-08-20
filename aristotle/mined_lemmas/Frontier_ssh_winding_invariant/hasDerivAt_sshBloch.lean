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

lemma hasDerivAt_sshBloch (v w : ℂ) (k : ℝ) :
    HasDerivAt (sshBloch v w) (w * Complex.I * Complex.exp (k * Complex.I)) k := by
  have h1 : HasDerivAt (fun k : ℝ => (k : ℂ) * Complex.I) Complex.I k := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := k)).mul_const Complex.I
  have h2 : HasDerivAt (fun k : ℝ => Complex.exp ((k : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h1.cexp
  have h3 := (h2.const_mul w).const_add v
  have hfun : sshBloch v w = fun k : ℝ => v + w * Complex.exp ((k : ℂ) * Complex.I) := rfl
  rw [hfun]
  convert h3 using 1
  ring

