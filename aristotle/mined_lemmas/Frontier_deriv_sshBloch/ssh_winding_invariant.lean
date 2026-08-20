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

theorem ssh_winding_invariant (v w : ℝ) (hw : 0 < w) (hgap : |v| ≠ w) :
    (∀ k : ℝ, sshBloch v w k ≠ 0) ∧
      ∃ n : ℤ, sshWinding v w = (n : ℂ) ∧ n = if |v| < w then 1 else 0 := by
  refine ⟨sshBloch_ne_zero v w hw hgap, ?_⟩
  rcases lt_or_gt_of_ne hgap with hlt | hgt
  · exact ⟨1, by simpa using sshWinding_topological v w hlt, by simp [hlt]⟩
  · exact ⟨0, by simpa using sshWinding_trivial v w hw hgt, by simp [not_lt.2 hgt.le]⟩

/-- Auxiliary sign-constancy: a continuous nowhere-vanishing function on `[0,1]` keeps its sign. -/
