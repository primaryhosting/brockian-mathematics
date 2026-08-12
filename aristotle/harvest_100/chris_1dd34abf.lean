import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct

namespace QC

/-- A single qubit space `ℂ²`, with its Hermitian (Euclidean) inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`. Mathlib's inner product on a tensor product of inner
product spaces is determined by `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`
(`TensorProduct.instInnerProductSpace`). -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis kets `|0⟩`, `|1⟩` of a single qubit. -/
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i (1 : ℂ)

/-- The computational basis kets `|ij⟩ = |i⟩ ⊗ |j⟩` of a two-qubit system. -/
noncomputable def ket2 (i j : Fin 2) : TwoQubit := ket i ⊗ₜ[ℂ] ket j

lemma inner_ket2 (i j k l : Fin 2) :
    inner ℂ (ket2 i j) (ket2 k l)
      = (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) := by
  simp [ket2, ket, TensorProduct.inner_tmul, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply]

/-- The normalization constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    field_simp
    linarith [h2]
  simp only [invSqrt2, ← Complex.ofReal_mul, h]
  norm_num

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, Complex.conj_ofReal]

/- Versions of the standard sesquilinearity lemmas whose statements are elaborated with the
`TensorProduct` scalar-multiplication and addition instances, so that they are usable as
rewrite rules on `TwoQubit`. -/

lemma tp_inner_smul_left (r : ℂ) (x y : TwoQubit) :
    inner ℂ (r • x) y = (starRingEnd ℂ) r * inner ℂ x y := inner_smul_left x y r

lemma tp_inner_smul_right (r : ℂ) (x y : TwoQubit) :
    inner ℂ x (r • y) = r * inner ℂ x y := inner_smul_right x y r

lemma tp_inner_add_left (x y z : TwoQubit) :
    inner ℂ (x + y) z = inner ℂ x z + inner ℂ y z := inner_add_left x y z

lemma tp_inner_add_right (x y z : TwoQubit) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z := inner_add_right x y z

/-- A normalized two-term combination `(|ab⟩ + s • |cd⟩)/√2` of computational basis states.
Each Bell state is of this shape with `s = ±1`. -/
noncomputable def combo (a b c d : Fin 2) (s : ℂ) : TwoQubit :=
  invSqrt2 • (ket2 a b + s • ket2 c d)

lemma inner_combo (a b c d a' b' c' d' : Fin 2) (s t : ℂ) :
    inner ℂ (combo a b c d s) (combo a' b' c' d' t)
      = (1 / 2 : ℂ) * ((if a = a' then 1 else 0) * (if b = b' then 1 else 0)
        + t * ((if a = c' then 1 else 0) * (if b = d' then 1 else 0))
        + (starRingEnd ℂ) s * ((if c = a' then 1 else 0) * (if d = b' then 1 else 0))
        + (starRingEnd ℂ) s * t * ((if c = c' then 1 else 0) * (if d = d' then 1 else 0))) := by
  simp only [combo, tp_inner_smul_left, tp_inner_smul_right, tp_inner_add_left,
    tp_inner_add_right, inner_ket2, conj_invSqrt2]
  linear_combination ((if a = a' then (1 : ℂ) else 0) * (if b = b' then 1 else 0)
    + t * ((if a = c' then 1 else 0) * (if b = d' then 1 else 0))
    + (starRingEnd ℂ) s * ((if c = a' then 1 else 0) * (if d = b' then 1 else 0))
    + (starRingEnd ℂ) s * t * ((if c = c' then 1 else 0) * (if d = d' then 1 else 0)))
      * invSqrt2_mul_self

/-- The four Bell states
`Φ⁺ = (|00⟩ + |11⟩)/√2`, `Φ⁻ = (|00⟩ - |11⟩)/√2`,
`Ψ⁺ = (|01⟩ + |10⟩)/√2`, `Ψ⁻ = (|01⟩ - |10⟩)/√2`. -/
noncomputable def bell : Fin 4 → TwoQubit :=
  ![combo 0 0 1 1 1, combo 0 0 1 1 (-1), combo 0 1 1 0 1, combo 0 1 1 0 (-1)]

/-- The four Bell states are orthonormal. -/
theorem bell_orthonormal_aux : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [bell, Fin.reduceFinMk, Matrix.cons_val] <;>
    rw [inner_combo] <;> norm_num <;> decide

lemma finrank_twoQubit : Module.finrank ℂ TwoQubit = 4 := by
  rw [Module.finrank_tensorProduct]
  simp

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are orthonormal
and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  refine ⟨bell_orthonormal_aux, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
    rw [Fintype.card_fin, finrank_twoQubit]
  have h := (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_aux hcard).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank bell_orthonormal_aux hcard] at h

end QC

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

