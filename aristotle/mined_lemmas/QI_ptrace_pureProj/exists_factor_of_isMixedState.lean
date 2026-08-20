import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/

theorem exists_factor_of_isMixedState {n : Type*} [Fintype n] [DecidableEq n]
    {rho : Matrix n n ℂ} (h : IsMixedState rho) :
    ∃ A : Matrix n n ℂ, A * Aᴴ = rho ∧ ∑ a : n × n, ‖A a.1 a.2‖ ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hb
  have hA : bᴴ * (bᴴ)ᴴ = rho := by rw [Matrix.conjTranspose_conjTranspose, ← hb]
  refine ⟨bᴴ, hA, ?_⟩
  have key : ((∑ a : n × n, ‖bᴴ a.1 a.2‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h.trace_eq_one, ← hA]
    push_cast
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast key

end Crux

section Main

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Purification.** Every mixed state `rho` has a purification (with ancilla a copy of the
system), and any two purifications of `rho` are related by an isometry acting on the ancilla
alone; when the two ancillas have the same dimension this isometry is a unitary. -/
