import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

/-!
## Setting

A state of a finite dimensional quantum system with basis indexed by `n` is a positive
semidefinite matrix `ρ : Matrix n n ℂ` of trace one.

A vector of the composite system `H ⊗ K`, where `K` is an ancilla with basis indexed by `m`,
is encoded by its matrix of coefficients `A : Matrix n m ℂ`, i.e. `A` encodes
`∑ i, ∑ j, A i j • (e i ⊗ f j)`.  With this encoding the reduced density matrix
(the partial trace over the ancilla) of the pure state `|A⟩⟨A|` is exactly `A * Aᴴ`, and the
squared norm of the vector is `∑ i, ∑ j, ‖A i j‖ ^ 2 = trace (A * Aᴴ)`.

Consequently `A` purifies `ρ` exactly when `A * Aᴴ = ρ`, and an isometry `K → K'` of ancillas
acting on the second tensor factor sends the vector `A` to `A * W`, where `W : Matrix m m' ℂ`
satisfies `W * Wᴴ = 1`.
-/

/-- `A` is a purification of the state `ρ`: the reduced density matrix (partial trace over the
ancilla) of the pure state given by the vector with coefficient matrix `A` equals `ρ`. -/

theorem purification_unit_norm {n m : Type*} [Fintype n] [Fintype m] {ρ : Matrix n n ℂ}
    (htr : ρ.trace = 1) {A : Matrix n m ℂ} (hA : IsPurification ρ A) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 := by
  have h : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← htr, ← hA]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.sq_norm (A i j)
  exact_mod_cast h

/-- Any two purifications of the same state are related by an isometry acting on the ancilla:
if `A` (ancilla `m`) and `B` (ancilla `m'`) both purify `ρ` and the ancilla `m` is no bigger
than `m'`, then there is an isometry `W` (`W * Wᴴ = 1`) with `A * W = B`. -/
