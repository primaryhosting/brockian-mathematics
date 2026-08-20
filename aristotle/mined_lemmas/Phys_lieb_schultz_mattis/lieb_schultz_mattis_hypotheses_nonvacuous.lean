import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

/-! ## The abstract twist argument

The Lieb–Schultz–Mattis theorem states that a translation invariant spin chain with
half-integer spin per site cannot have a unique ground state separated by a spectral gap:
it is either gapless (in the thermodynamic limit) or has a degenerate ground state.

The mechanism, discovered by Lieb, Schultz and Mattis, is the *twist* (or *large gauge
transformation*) operator `U = exp (2πi/L ∑ j Sᶻⱼ)`.  Applied to the ground state it
produces a variational state whose energy exceeds the ground state energy by `O(1/L)`,
and whose momentum is shifted by exactly `π` relative to the ground state precisely
because the spin per site is half-integer.  The momentum shift forces the twisted state
to be orthogonal to the ground state, so it is a genuine low lying excitation.

`Phys.lieb_schultz_mattis` below is the general form of this argument in an arbitrary
complex inner product space: `T` is the (isometric) translation operator, `psi` a
ground state of momentum `c`, `U` the twist operator, and the hypothesis `hshift`
records the half-integer-spin momentum shift `T (U psi) = -c • (U psi)`.  The
conclusion says that the spectral gap above `psi` is at most `eps`: there is a unit
state orthogonal to `psi` whose energy is within `eps` of the ground state energy
(degeneracy when `eps = 0`, gaplessness in the thermodynamic limit when `eps = O(1/L)`).

In `Phys.SpinChain` the momentum shift hypothesis is *derived* for the concrete
spin-`1/2` chain of `L` sites in the zero magnetization sector, see
`Phys.SpinChain.trans_twist_anticomm` and
`Phys.SpinChain.lieb_schultz_mattis_spin_half_chain`.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The energy expectation value `⟪x, A x⟫` of a state `x` for the Hamiltonian `A`. -/

theorem lieb_schultz_mattis_hypotheses_nonvacuous :
    ∃ (A T U : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (psi : EuclideanSpace ℂ (Fin 2)) (c : ℂ) (eps : ℝ),
      (∀ x y, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ ‖psi‖ = 1 ∧ T psi = c • psi ∧
      T (U psi) = -(c • U psi) ∧ ‖U psi‖ = 1 ∧
      energy A (U psi) ≤ energy A psi + eps ∧ U psi ≠ psi := by
  have hpos : (0 : ℝ) < ((Real.sqrt 2)⁻¹ : ℝ) := by positivity
  have hval : ∀ i, plusState i = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := fun _ => rfl
  have hnorm : ‖plusState‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [hval, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hpos.le]
    rw [show ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 + ((Real.sqrt 2)⁻¹ : ℝ) ^ 2
        = ((Real.sqrt 2) ^ 2)⁻¹ * 2 by ring, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨0, pauliX, pauliZ, plusState, 1, 0, ?_, hnorm, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y => permOp_inner (Equiv.swap 0 1) x y
  · ext i
    simp [pauliX, hval]
  · ext i
    fin_cases i <;> simp [pauliX, pauliZ, hval]
  · rw [pauliZ, norm_diagOp _ (fun i => by by_cases h : i = 0 <;> simp [h]), hnorm]
  · simp [energy]
  · intro h
    have h1 : pauliZ plusState 1 = plusState 1 := by rw [h]
    simp only [pauliZ, diagOp_apply, hval] at h1
    norm_num at h1
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 0 := by linear_combination -h1 / 2
    rw [inv_eq_zero, Complex.ofReal_eq_zero] at h2
    rw [h2] at hpos
    simp at hpos

end NonVacuous

end Phys

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

