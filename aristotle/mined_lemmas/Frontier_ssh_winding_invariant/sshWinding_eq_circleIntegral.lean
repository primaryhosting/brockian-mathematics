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

lemma sshWinding_eq_circleIntegral (v w : ℂ) :
    sshWinding v w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(0, 1), w / (v + w * z) := by
  unfold sshWinding
  congr 1
  rw [circleIntegral]
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_circleMap, circleMap, smul_eq_mul, deriv_sshBloch, sshBloch,
    Complex.ofReal_one, one_mul, zero_add]
  ring

/-- Trivial phase: if the intracell hopping dominates (`‖w‖ < ‖v‖`), the winding number is `0`. -/
