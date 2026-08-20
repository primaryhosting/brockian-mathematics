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
def tensor (x y : Qubit) : Qubit2 := WithLp.toLp 2 (fun p => x.ofLp p.1 * y.ofLp p.2)

/-- Inner products of product states factor: `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
lemma inner_tensor_tensor (a b c d : Qubit) :
    inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d := by
  simp [PiLp.inner_apply, RCLike.inner_apply, tensor, Fintype.sum_prod_type]
  ring

/-- The computational basis state `|0⟩`. -/
def e0 : Qubit := WithLp.toLp 2 ![1, 0]

/-- An auxiliary unit vector `(3/5)|0⟩ + (4/5)|1⟩`, at inner product `3/5` with `|0⟩`. -/
def w : Qubit := WithLp.toLp 2 ![3 / 5, 4 / 5]

lemma norm_e0 : ‖e0‖ = 1 := by
  simp [EuclideanSpace.norm_eq, e0, Fin.sum_univ_two]

lemma norm_w : ‖w‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [w, Fin.sum_univ_two]

lemma inner_e0_w : inner ℂ e0 w = (3 / 5 : ℂ) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, e0, w, Fin.sum_univ_two]

/-!
## The key intermediate lemma

Any map preserving inner products which deletes would force `⟪ψ, φ⟫ ^ 2 = ⟪ψ, φ⟫`
for all unit vectors `ψ, φ`, since
`⟪ψ ⊗ ψ, φ ⊗ φ⟫ = ⟪ψ, φ⟫ ^ 2` while `⟪ψ ⊗ |0⟩, φ ⊗ |0⟩⟫ = ⟪ψ, φ⟫`.
This is impossible: the overlap of two unit vectors can be `3/5`, and `(3/5)^2 ≠ 3/5`.
-/

/-- Key lemma: there is no inner-product preserving map that deletes an unknown qubit. -/
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
theorem no_deleting :
    ¬ ∃ U : Qubit2 ≃ₗᵢ[ℂ] Qubit2, ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tensor ψ ψ) = tensor ψ e0 := by
  rintro ⟨U, hdel⟩
  exact no_deleting_of_inner_preserving ⟨U, fun x y => U.inner_map_map x y, hdel⟩

end

end QI

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

