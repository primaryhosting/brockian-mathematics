/-
/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
## Formalization

We work with a single qubit `Qubit = EuclideanSpace ℂ (Fin 2)` and the two-qubit space
`Qubit2 = EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the product state `tens x y` given by
`(x ⊗ y) (i, j) = x i * y j`.

A *deleting machine* would be a unitary `U` on the two-qubit space together with a fixed
blank state `s` (a unit vector) such that `U (x ⊗ x) = x ⊗ s` for every unit vector `x`,
i.e. the second copy of the unknown state `x` is erased and replaced by a state that does
not depend on `x`.  The no-deleting theorem says no such unitary exists: unitaries preserve
inner products, so `⟪x, y⟫ ^ 2 = ⟪x, y⟫ ⟪s, s⟫ = ⟪x, y⟫` for all unit `x, y`, which fails
for e.g. `x = (1, 0)` and `y = (3/5, 4/5)`.
-/

namespace QI

open scoped InnerProductSpace ComplexConjugate

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits. -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product (tensor) state `x ⊗ y`. -/
def tens (x y : Qubit) : Qubit2 := WithLp.toLp 2 (fun p => x.ofLp p.1 * y.ofLp p.2)

/-- Inner products of product states factor. -/
lemma inner_tens (x y x' y' : Qubit) :
    ⟪tens x y, tens x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, PiLp.inner_apply, PiLp.inner_apply,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [tens, WithLp.ofLp_toLp, RCLike.inner_apply', map_mul]
  ring

/-- A unit vector of the qubit space. -/
def stateA : Qubit := WithLp.toLp 2 ![1, 0]

/-- Another unit vector, not orthogonal to `stateA` and different from it. -/
noncomputable def stateB : Qubit := WithLp.toLp 2 ![3 / 5, 4 / 5]

lemma norm_stateA : ‖stateA‖ = 1 := by
  simp [stateA, EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma norm_stateB : ‖stateB‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ i, ‖(stateB.ofLp i)‖ ^ 2 = 1 := by
    simp [stateB, Fin.sum_univ_two]
    norm_num
  rw [this, Real.sqrt_one]

lemma inner_stateA_stateB : ⟪stateA, stateB⟫_ℂ = 3 / 5 := by
  simp [stateA, stateB, PiLp.inner_apply, Fin.sum_univ_two]

/-- **No-deleting theorem.**  There is no unitary `U` on two qubits and blank unit state `s`
with `U (x ⊗ x) = x ⊗ s` for every unit state `x`: an unknown quantum state cannot be
deleted. -/
theorem no_deleting :
    ¬ ∃ (U : Qubit2 ≃ₗᵢ[ℂ] Qubit2) (s : Qubit), ‖s‖ = 1 ∧
      ∀ x : Qubit, ‖x‖ = 1 → U (tens x x) = tens x s := by
  rintro ⟨U, s, hs, hU⟩
  have hss : ⟪s, s⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hs]
    norm_num
  have key : ⟪tens stateA stateA, tens stateB stateB⟫_ℂ
      = ⟪tens stateA s, tens stateB s⟫_ℂ := by
    rw [← hU stateA norm_stateA, ← hU stateB norm_stateB, U.inner_map_map]
  rw [inner_tens, inner_tens, inner_stateA_stateB, hss] at key
  norm_num at key

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

