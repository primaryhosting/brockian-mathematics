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

private lemma mem_unitaryGroup_of_dotProduct (W : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, star (W *ᵥ x) ⬝ᵥ (W *ᵥ y) = star x ⬝ᵥ y) :
    W ∈ Matrix.unitaryGroup m ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have h1 := h (Pi.single j 1) (Pi.single k 1)
  rw [dotProduct_conj_mulVec] at h1
  have hs : star (Pi.single j (1 : ℂ) : m → ℂ) = Pi.single j 1 := by
    ext i; simp [Pi.single_apply, apply_ite]
  rw [hs, single_one_dotProduct, single_one_dotProduct, Matrix.mulVec_single_one] at h1
  simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, Pi.single_apply, eq_comm] using h1

