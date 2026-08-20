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

theorem exists_isometry_matrix {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] (h : Fintype.card m ≤ Fintype.card m') :
    ∃ J : Matrix m' m ℂ, Jᴴ * J = 1 := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h
  refine ⟨Matrix.of fun (i : m') (j : m) => if i = f j then (1 : ℂ) else 0, ?_⟩
  ext j k
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
    apply_ite star, star_one, star_zero]
  rw [Finset.sum_eq_single (f j)]
  · simp [f.injective.eq_iff]
  · intro b _ hb
    simp [hb]
  · intro hb
    exact absurd (Finset.mem_univ (f j)) hb

/-! ## Purification -/

/-- The canonical purification: the positive semidefinite square root of `ρ`. -/
