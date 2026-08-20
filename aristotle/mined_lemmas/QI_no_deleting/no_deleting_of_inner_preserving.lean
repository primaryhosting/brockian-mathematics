import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setup

We work with a single qubit `Qubit = EuclideanSpace ℂ (Fin 2)` and the two-qubit space
`Qubit2 = EuclideanSpace ℂ (Fin 2 × Fin 2)`, which is the tensor square of `Qubit`
(with the product basis indexed by `Fin 2 × Fin 2`).

A *deleting machine* would be a unitary `U` on the two-qubit space with
`U (ψ ⊗ ψ) = ψ ⊗ |0⟩` for every unit vector `ψ`, i.e. it erases the second copy of an
unknown state.  The no-deleting theorem says no such unitary exists.
-/

namespace QI

noncomputable section

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. the tensor square of `Qubit`. -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product (tensor) state `x ⊗ y`. -/

theorem no_deleting_of_inner_preserving :
    ¬ ∃ U : Qubit2 → Qubit2,
        (∀ x y : Qubit2, inner ℂ (U x) (U y) = inner ℂ x y) ∧
        (∀ ψ : Qubit, ‖ψ‖ = 1 → U (tensor ψ ψ) = tensor ψ e0) := by
  rintro ⟨U, hU, hdel⟩
  -- Overlaps must satisfy `c ^ 2 = c` for all unit vectors.
  have key : ∀ ψ φ : Qubit, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      inner ℂ ψ φ * inner ℂ ψ φ = inner ℂ ψ φ := by
    intro ψ φ hψ hφ
    have h1 : inner ℂ (U (tensor ψ ψ)) (U (tensor φ φ)) = inner ℂ (tensor ψ ψ) (tensor φ φ) :=
      hU _ _
    rw [hdel ψ hψ, hdel φ hφ, inner_tensor_tensor, inner_tensor_tensor] at h1
    have h0 : inner ℂ e0 e0 = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, norm_e0]
      norm_num
    rw [h0, mul_one] at h1
    exact h1.symm
  have := key e0 w norm_e0 norm_w
  rw [inner_e0_w] at this
  norm_num at this

/-- **No-deleting theorem.**  There is no unitary (linear isometric equivalence) `U` on the
two-qubit space which, for every unit vector `ψ`, maps `ψ ⊗ ψ` to `ψ ⊗ |0⟩`; that is, no
unitary can delete an unknown quantum state. -/
