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

open Complex Metric

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is `H(k) = Re h(k) • σₓ + Im h(k) • σ_y`,
so the spectral gap is open exactly when `h(k) ≠ 0` for all `k`. -/

theorem ssh_winding_integer (v w : ℝ) (hw : 0 ≤ w) (h : |v| ≠ w) :
    ∃ n : ℤ, sshWinding v w = (n : ℂ) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ⟨1, by rw [sshWinding_of_abs_lt v w hlt]; norm_num⟩
  · exact ⟨0, by rw [sshWinding_of_lt_abs v w hw hgt]; norm_num⟩

end Frontier

