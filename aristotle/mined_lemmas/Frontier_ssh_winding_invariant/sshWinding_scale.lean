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

lemma sshWinding_scale (c v w : ℂ) (hc : c ≠ 0) :
    sshWinding (c * v) (c * w) = sshWinding v w := by
  unfold sshWinding
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_sshBloch, sshBloch]
  have hnum : c * w * Complex.I * Complex.exp ((k : ℂ) * Complex.I)
      = c * (w * Complex.I * Complex.exp ((k : ℂ) * Complex.I)) := by ring
  have hden : c * v + c * w * Complex.exp ((k : ℂ) * Complex.I)
      = c * (v + w * Complex.exp ((k : ℂ) * Complex.I)) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hc]

/-- **SSH winding invariant.** The topological phase of the SSH model is classified by an
integer winding number of the off-diagonal Bloch function `h(k) = v + w e^{ik}`:
it vanishes in the trivial phase `‖w‖ < ‖v‖` and equals one in the topological
phase `‖v‖ < ‖w‖`. In particular the winding number is always an integer, and it jumps
only at the gap-closing point `‖v‖ = ‖w‖`. -/
