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

theorem sshBloch_ne_zero (v w : ℝ) (hw : 0 < w) (hgap : |v| ≠ w) (k : ℝ) :
    sshBloch v w k ≠ 0 := by
  intro h
  have h' : (w : ℂ) * Complex.exp (Complex.I * (k : ℂ)) = -(v : ℂ) := by
    have := h
    unfold sshBloch at this
    linear_combination this
  have habs : ‖(w : ℂ) * Complex.exp (Complex.I * (k : ℂ))‖ = ‖(-(v : ℂ))‖ := by rw [h']
  rw [norm_mul] at habs
  have hexp : ‖Complex.exp (Complex.I * (k : ℂ))‖ = 1 := by
    rw [mul_comm]
    simp
  rw [hexp, mul_one, norm_neg, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw] at habs
  exact hgap habs.symm

/-- The SSH winding integral is the contour integral of `z⁻¹` over the circle of radius `w`
centred at `v`: the Bloch loop `k ↦ v + w e^{ik}` is exactly that circle. -/
