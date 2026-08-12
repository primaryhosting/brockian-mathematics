/-
/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is reproduced verbatim as the module docstring below; Lean requires
-- `import` commands to precede any docstring command.)

import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
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

namespace QC

/-- The state space of a single qubit, `H = ℂ²` with its standard inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The state space of a pair of qubits, `H ⊗ H ≅ ℂ² ⊗ ℂ² ≅ ℂ^(2×2)`. -/
abbrev TwoQubit : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor (Kronecker) product of two qubit states: `(u ⊗ v) (i, j) = u i * v j`. -/
noncomputable def kron (u v : Qubit) : TwoQubit :=
  WithLp.toLp 2 (fun p => u.ofLp p.1 * v.ofLp p.2)

/-- The inner product on `H ⊗ H` factors through tensors:
`⟪u ⊗ v, u' ⊗ v'⟫ = ⟪u, u'⟫ * ⟪v, v'⟫`. -/
theorem inner_kron_kron (u v u' v' : Qubit) :
    inner ℂ (kron u v) (kron u' v') = inner ℂ u u' * inner ℂ v v' := by
  simp only [kron, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type, map_mul,
    Fin.sum_univ_two]
  ring

/-- The computational basis state `|0⟩`. -/
noncomputable def ket0 : Qubit := WithLp.toLp 2 ![1, 0]

/-- The uniform superposition `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def ketPlus : Qubit :=
  WithLp.toLp 2 ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹]

theorem norm_ket0 : ‖ket0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [ket0, Fin.sum_univ_two]

theorem norm_ketPlus : ‖ketPlus‖ = 1 := by
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 2, ‖(ketPlus.ofLp i)‖ ^ 2 = 1 := by
    simp [ketPlus, Fin.sum_univ_two, Complex.norm_real]
    field_simp
    norm_num
  rw [hsum, Real.sqrt_one]

theorem inner_self_ket0 : inner ℂ ket0 ket0 = 1 := by
  simp only [ket0, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem inner_ket0_ketPlus : inner ℂ ket0 ketPlus = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [ket0, ketPlus, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]

/-- **No cloning, abstract form.** Let `H` and `E` be complex inner product spaces and let
`ten : H → H → E` be a "tensor product" pairing, i.e. one satisfying
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. If `H` contains two states `u`, `v` whose overlap
`⟪u, v⟫` is neither `0` nor `1` (i.e. they are neither orthogonal nor equal up to phase),
then no unitary `U` on `E` can clone: `U (ψ ⊗ e₀) = ψ ⊗ ψ` cannot hold for all states `ψ`.

The proof is the standard one: unitaries preserve inner products, so the overlap `c = ⟪u, v⟫`
would satisfy `c * c = c`, forcing `c ∈ {0, 1}`. -/
theorem no_cloning_general {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ten : H → H → E)
    (hten : ∀ a b c d, inner ℂ (ten a b) (ten c d) = inner ℂ a c * inner ℂ b d)
    (e0 u v : H) (he0 : ‖e0‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h0 : inner ℂ u v ≠ 0) (h1 : inner ℂ u v ≠ 1) :
    ¬ ∃ U : E ≃ₗᵢ[ℂ] E, ∀ psi : H, ‖psi‖ = 1 → U (ten psi e0) = ten psi psi := by
  rintro ⟨U, hU⟩
  have hself : inner ℂ e0 e0 = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, he0]; norm_num
  have key : (inner ℂ u v : ℂ) * inner ℂ u v = 1 * inner ℂ u v := by
    have h := U.inner_map_map (ten u e0) (ten v e0)
    rw [hU u hu, hU v hv, hten, hten, hself, mul_one] at h
    rw [one_mul]; exact h
  exact h1 (mul_right_cancel₀ h0 key)

theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, hs]

/-- **No-cloning theorem.** There is no unitary operator `U` on `H ⊗ H` (with `H = ℂ²`) such
that `U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state (unit vector) `|ψ⟩`. -/
theorem no_cloning :
    ¬ ∃ U : TwoQubit ≃ₗᵢ[ℂ] TwoQubit,
        ∀ psi : Qubit, ‖psi‖ = 1 → U (kron psi ket0) = kron psi psi := by
  have hpos : (0:ℝ) < Real.sqrt 2 := lt_trans one_pos one_lt_sqrt_two
  refine no_cloning_general kron inner_kron_kron ket0 ket0 ketPlus norm_ket0 norm_ket0
    norm_ketPlus ?_ ?_
  · rw [inner_ket0_ketPlus]
    simp
  · rw [inner_ket0_ketPlus]
    have hne : ((Real.sqrt 2)⁻¹ : ℝ) ≠ 1 := by
      intro h
      rw [inv_eq_one_div, div_eq_one_iff_eq (ne_of_gt hpos)] at h
      linarith [one_lt_sqrt_two]
    exact_mod_cast hne

end QC

