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

theorem ssh_winding_invariant (v w : ℂ) :
    (‖w‖ < ‖v‖ → sshWinding v w = 0) ∧ (‖v‖ < ‖w‖ → sshWinding v w = 1) ∧
      (‖w‖ ≠ ‖v‖ → ∃ n : ℤ, sshWinding v w = (n : ℂ)) := by
  refine ⟨sshWinding_eq_zero_of_norm_lt v w, sshWinding_eq_one_of_norm_lt v w, ?_⟩
  intro hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨0, by rw [sshWinding_eq_zero_of_norm_lt v w hlt]; norm_num⟩
  · exact ⟨1, by rw [sshWinding_eq_one_of_norm_lt v w hgt]; norm_num⟩

end Frontier

