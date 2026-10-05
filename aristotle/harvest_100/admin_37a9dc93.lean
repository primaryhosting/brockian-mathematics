/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/-- A qubit, i.e. a vector of the two-dimensional complex Hilbert space, given by its two
amplitudes. -/
noncomputable def qubit (x y : ℂ) : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![x, y]

@[simp] lemma qubit_apply (x y : ℂ) (i : Fin 2) : qubit x y i = ![x, y] i := rfl

/-- The state space of two qubits together with an ancilla register indexed by `α`. -/
abbrev Sys (α : Type*) := EuclideanSpace ℂ (Fin 2 × Fin 2 × α)

/-- The product (tensor) state `u ⊗ v ⊗ a` of two qubits and an ancilla state. -/
noncomputable def reg3 {α : Type*} [Fintype α] (u v : EuclideanSpace ℂ (Fin 2))
    (a : EuclideanSpace ℂ α) : Sys α :=
  WithLp.toLp 2 (fun p => u p.1 * v p.2.1 * a p.2.2)

@[simp] lemma reg3_apply {α : Type*} [Fintype α] (u v : EuclideanSpace ℂ (Fin 2))
    (a : EuclideanSpace ℂ α) (p : Fin 2 × Fin 2 × α) :
    reg3 u v a p = u p.1 * v p.2.1 * a p.2.2 := rfl

/-- Expansion of a product state of two qubits in the computational product basis. -/
lemma reg3_expand {α : Type*} [Fintype α] (x y z w : ℂ) (a : EuclideanSpace ℂ α) :
    reg3 (qubit x y) (qubit z w) a
      = (x * z) • reg3 (qubit 1 0) (qubit 1 0) a + (x * w) • reg3 (qubit 1 0) (qubit 0 1) a
        + (y * z) • reg3 (qubit 0 1) (qubit 1 0) a + (y * w) • reg3 (qubit 0 1) (qubit 0 1) a := by
  ext p
  obtain ⟨i, j, k⟩ := p
  fin_cases i <;> fin_cases j <;> simp

lemma norm_qubit_of (x y : ℂ) (h : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) : ‖qubit x y‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [qubit, Fin.sum_univ_two, h]

lemma norm_qubit_one_zero : ‖qubit 1 0‖ = 1 := norm_qubit_of 1 0 (by norm_num)

lemma norm_qubit_zero_one : ‖qubit 0 1‖ = 1 := norm_qubit_of 0 1 (by norm_num)

/-- The real number `1 / √2`, as a complex number. -/
noncomputable def half : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma norm_half : ‖half‖ = (Real.sqrt 2)⁻¹ := by
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  simp [half, Complex.norm_real, abs_of_pos h2]

lemma norm_half_sq : ‖half‖ ^ 2 = 2⁻¹ := by
  rw [norm_half, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma half_mul_half : half * half = (2:ℂ)⁻¹ := by
  have : ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = (2:ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [half, ← Complex.ofReal_mul, this]
  norm_num

lemma norm_qubit_plus : ‖qubit half half‖ = 1 :=
  norm_qubit_of _ _ (by rw [norm_half_sq]; norm_num)

lemma norm_qubit_minus : ‖qubit half (-half)‖ = 1 :=
  norm_qubit_of _ _ (by rw [norm_neg, norm_half_sq]; norm_num)

/-- `U` deletes the second copy of an unknown qubit: starting from `u ⊗ u ⊗ a` (two copies of an
arbitrary unknown qubit state `u`, together with a fixed ancilla state `a`) it produces
`u ⊗ b ⊗ a'`, where the "blank" state `b` and the final ancilla state `a'` do not depend on the
deleted state `u`. -/
def Deletes {α : Type*} [Fintype α] (U : Sys α ≃ₗᵢ[ℂ] Sys α)
    (a : EuclideanSpace ℂ α) (b : EuclideanSpace ℂ (Fin 2)) (a' : EuclideanSpace ℂ α) : Prop :=
  ∀ u : EuclideanSpace ℂ (Fin 2), ‖u‖ = 1 → U (reg3 u u a) = reg3 u b a'

/-- **No-deleting theorem.** There is no unitary operation on two qubits together with an ancilla
register that deletes one of two identical copies of an unknown qubit state, leaving behind a
fixed blank state and a fixed final ancilla state.

Formally: for a nonzero ancilla state `a`, no unitary `U` (a surjective linear isometry of the
composite state space) satisfies `U (u ⊗ u ⊗ a) = u ⊗ b ⊗ a'` for every unit qubit state `u`,
whatever the blank state `b` and the final ancilla state `a'` are. -/
theorem no_deleting {α : Type*} [Fintype α] (U : Sys α ≃ₗᵢ[ℂ] Sys α)
    (a : EuclideanSpace ℂ α) (b : EuclideanSpace ℂ (Fin 2)) (a' : EuclideanSpace ℂ α)
    (ha : a ≠ 0) : ¬ Deletes U a b a' := by
  intro h
  -- the four images of the computational basis product states
  set A := U (reg3 (qubit 1 0) (qubit 1 0) a) with hA
  set B := U (reg3 (qubit 1 0) (qubit 0 1) a) with hB
  set C := U (reg3 (qubit 0 1) (qubit 1 0) a) with hC
  set D := U (reg3 (qubit 0 1) (qubit 0 1) a) with hD
  have h0 : A = reg3 (qubit 1 0) b a' := h _ norm_qubit_one_zero
  have h1 : D = reg3 (qubit 0 1) b a' := h _ norm_qubit_zero_one
  have hp := h _ norm_qubit_plus
  have hm := h _ norm_qubit_minus
  rw [reg3_expand, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    ← hA, ← hB, ← hC, ← hD] at hp hm
  -- evaluate at coordinates whose first index is `1`
  have key : ∀ (j : Fin 2) (k : α), b j * a' k = 0 := by
    intro j k
    have hpk := congrArg (fun v : Sys α => v (1, j, k)) hp
    have hmk := congrArg (fun v : Sys α => v (1, j, k)) hm
    have h0k := congrArg (fun v : Sys α => v (1, j, k)) h0
    have h1k := congrArg (fun v : Sys α => v (1, j, k)) h1
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, reg3_apply, qubit_apply,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hpk hmk h0k h1k
    have hsum : A (1, j, k) + D (1, j, k) = 0 := by
      linear_combination hpk + hmk
        - (2 * A (1, j, k) + 2 * D (1, j, k)) * half_mul_half
    rw [h0k, h1k] at hsum
    simpa using hsum
  -- hence `U` maps a nonzero vector to zero
  have hAzero : A = 0 := by
    rw [h0]
    ext p
    obtain ⟨i, j, k⟩ := p
    simp [mul_assoc, key j k]
  rw [hA] at hAzero
  have hzero : reg3 (qubit 1 0) (qubit 1 0) a = 0 := by
    have := congrArg U.symm hAzero
    simpa using this
  apply ha
  ext k
  have := congrArg (fun v : Sys α => v (0, 0, k)) hzero
  simpa using this

/-- The swap of the second qubit register with a (qubit) ancilla register. -/
def swapLast : (Fin 2 × Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2) where
  toFun p := (p.1, p.2.2, p.2.1)
  invFun p := (p.1, p.2.2, p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sharpness of `QI.no_deleting`: the hypothesis that the final ancilla state does not depend on
the deleted state cannot be dropped. Swapping the second qubit register with the ancilla register
is a unitary that does turn `u ⊗ u ⊗ |0⟩` into `u ⊗ |0⟩ ⊗ u`, i.e. it erases the second copy of
`u`, but only at the price of moving it into the ancilla. -/
lemma deleting_into_ancilla :
    ∃ U : Sys (Fin 2) ≃ₗᵢ[ℂ] Sys (Fin 2), ∀ u : EuclideanSpace ℂ (Fin 2),
      U (reg3 u u (qubit 1 0)) = reg3 u (qubit 1 0) u := by
  refine ⟨LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ swapLast, fun u => ?_⟩
  ext p
  obtain ⟨i, j, k⟩ := p
  simp [reg3, swapLast, LinearIsometryEquiv.piLpCongrLeft_apply]
  ring

end QI

