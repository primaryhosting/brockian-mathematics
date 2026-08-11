/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Statement: There is no unitary that deletes an unknown quantum state (no-deleting theorem).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Statement: There is no unitary that deletes an unknown quantum state (no-deleting theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexConjugate

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

namespace QI

/-- A qubit: the two-dimensional complex Hilbert space. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The register of a deleting machine: two qubits together with an ancilla indexed by `ι`.
Concretely this is the Hilbert space `ℂ^(2 × 2 × ι)`, which is the tensor product of two
qubit spaces with the ancilla space `ℂ^ι`. -/
abbrev Register (ι : Type) : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × ι)

/-- The product (tensor) state `x ⊗ y ⊗ a` of two qubits and an ancilla. -/
noncomputable def tens3 {ι : Type} (x y : Qubit) (a : EuclideanSpace ℂ ι) : Register ι :=
  WithLp.toLp 2 (fun p => x p.1 * y p.2.1 * a p.2.2)

/-- Inner products of product states factor as products of inner products. -/
theorem inner_tens3 {ι : Type} [Fintype ι] (x y x' y' : Qubit) (a a' : EuclideanSpace ℂ ι) :
    inner ℂ (tens3 x y a) (tens3 x' y' a') =
      inner ℂ x x' * inner ℂ y y' * inner ℂ a a' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, tens3, map_mul,
    Fintype.sum_prod_type, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  rw [Finset.sum_comm]

/-- A vector whose self-inner-product is `1` is a unit vector. -/
theorem norm_eq_one_of_inner_self {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x : E} (h : inner ℂ x x = (1 : ℂ)) : ‖x‖ = 1 := by
  have h2 : ((‖x‖ : ℂ)) ^ 2 = (1 : ℂ) := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x).symm.trans h
  have h3 : (‖x‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg x]

/-- The self-inner-product of a unit vector is `1`. -/
theorem inner_self_of_norm_eq_one {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x : E} (h : ‖x‖ = 1) : inner ℂ x x = (1 : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x, h]
  norm_num

/-- The blank state `|0⟩`, into which the second qubit is supposed to be erased. -/
noncomputable def ket0 : Qubit := WithLp.toLp 2 ![1, 0]

/-- The auxiliary qubit state `(3/5)|0⟩ + (4/5)|1⟩`, which is neither orthogonal nor equal
to `|0⟩`. -/
noncomputable def ketw : Qubit := WithLp.toLp 2 ![3 / 5, 4 / 5]

theorem inner_ket0_ket0 : inner ℂ ket0 ket0 = (1 : ℂ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, ket0, Fin.sum_univ_two]
  norm_num

theorem inner_ketw_ketw : inner ℂ ketw ketw = (1 : ℂ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, ketw, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_ofNat]
  norm_num

theorem inner_ket0_ketw : inner ℂ ket0 ketw = (3 / 5 : ℂ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, ket0, ketw, Fin.sum_univ_two]
  norm_num

theorem norm_ket0 : ‖ket0‖ = 1 := norm_eq_one_of_inner_self inner_ket0_ket0

theorem norm_ketw : ‖ketw‖ = 1 := norm_eq_one_of_inner_self inner_ketw_ketw

/-- **No deleting, quantitative form.**  Suppose a unitary `U` acting on two qubits plus an
ancilla, the latter initialised in the unit state `a`, maps every state `|x⟩|x⟩|a⟩` with `x` a
unit qubit state to `|x⟩|0⟩|A x⟩`, i.e. it erases the second copy of `x`.  Then the resulting
ancilla states retain all the overlaps of the supposedly deleted states:
`⟪A x, A y⟫ = ⟪x, y⟫` whenever `⟪x, y⟫ ≠ 0`.  In other words, the state was moved into the
ancilla, not destroyed. -/
theorem deleting_moves_state_to_ancilla {ι : Type} [Fintype ι]
    (a : EuclideanSpace ℂ ι) (ha : ‖a‖ = 1)
    (A : Qubit → EuclideanSpace ℂ ι)
    (U : Register ι ≃ₗᵢ[ℂ] Register ι)
    (hU : ∀ x : Qubit, ‖x‖ = 1 → U (tens3 x x a) = tens3 x ket0 (A x))
    (x y : Qubit) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : inner ℂ x y ≠ 0) :
    inner ℂ (A x) (A y) = inner ℂ x y := by
  have key : inner ℂ (U (tens3 x x a)) (U (tens3 y y a)) = inner ℂ (tens3 x x a) (tens3 y y a) :=
    U.inner_map_map _ _
  rw [hU x hx, hU y hy, inner_tens3, inner_tens3, inner_self_of_norm_eq_one ha,
    inner_ket0_ket0] at key
  have key' : inner ℂ x y * inner ℂ (A x) (A y) = inner ℂ x y * inner ℂ x y := by
    linear_combination key
  exact mul_left_cancel₀ hne key'

/-- **No-deleting theorem.**  There is no unitary that deletes an unknown quantum state:
no unitary `U` on two qubits plus an ancilla (initialised in a unit state `a`) can map
`|x⟩|x⟩|a⟩` to `|x⟩|0⟩|anc⟩` for every unit qubit state `x`, with a final ancilla state `anc`
that does not depend on `x`. -/
theorem no_deleting {ι : Type} [Fintype ι]
    (a : EuclideanSpace ℂ ι) (ha : ‖a‖ = 1) (anc : EuclideanSpace ℂ ι)
    (U : Register ι ≃ₗᵢ[ℂ] Register ι) :
    ¬ (∀ x : Qubit, ‖x‖ = 1 → U (tens3 x x a) = tens3 x ket0 anc) := by
  intro hU
  have hU' : ∀ x : Qubit, ‖x‖ = 1 → U (tens3 x x a) = tens3 x ket0 ((fun _ => anc) x) := hU
  have h1 : inner ℂ anc anc = inner ℂ ket0 ket0 :=
    deleting_moves_state_to_ancilla a ha (fun _ => anc) U hU' ket0 ket0 norm_ket0 norm_ket0
      (by rw [inner_ket0_ket0]; norm_num)
  have h2 : inner ℂ anc anc = inner ℂ ket0 ketw :=
    deleting_moves_state_to_ancilla a ha (fun _ => anc) U hU' ket0 ketw norm_ket0 norm_ketw
      (by rw [inner_ket0_ketw]; norm_num)
  rw [inner_ket0_ket0] at h1
  rw [inner_ket0_ketw, h1] at h2
  norm_num at h2

end QI

