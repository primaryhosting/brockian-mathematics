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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
chain with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The two-band Hamiltonian is
`H(k) = [[0, h(k)], [conj (h k), 0]]`, whose spectral gap is open iff `h k ≠ 0`. -/

noncomputable def sshH (v w : ℝ) (k : ℝ) : ℂ := (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH model: the number of times the loop
`k ↦ h(k)`, `k ∈ [0, 2π]`, winds around the origin, computed as
`(2π i)⁻¹ ∫₀^{2π} h'(k) / h(k) dk`. -/
