import Mathlib

/-!
# Purification of mixed states

A *mixed state* on a finite-dimensional system with index type `n` is a positive semidefinite
matrix `rho : Matrix n n ℂ` of trace `1`.  A *purification* of `rho` with ancilla index type `m`
is a vector `v : n × m → ℂ` in the tensor product whose density matrix `|v⟩⟨v|` has partial
trace over the ancilla equal to `rho`.

The main result `QI.purification_exists` states that every mixed state admits a purification
(with ancilla of the same dimension), and that any two purifications with the same ancilla
differ by a unitary acting on the ancilla alone.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

set_option synthInstance.maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The density matrix `|v⟩⟨v|` of the vector `v`. -/

theorem sum_norm_sq_of_isPurification {rho : Matrix n n ℂ} {v : n × m → ℂ}
    (hv : IsPurification rho v) (h1 : rho.trace = 1) :
    ∑ x : n × m, ‖v x‖ ^ 2 = 1 := by
  have hz : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  have h2 : ((∑ x : n × m, ‖v x‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1, ← hv]
    simp [Matrix.trace, Matrix.diag, ptraceSnd, outer, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type, hz]
  exact_mod_cast h2

/-! ### Linear algebra input: unitary freedom -/

