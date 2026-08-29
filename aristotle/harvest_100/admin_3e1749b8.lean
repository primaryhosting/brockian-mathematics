/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate TensorProduct

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realized as the Hilbert space of functions on the
product index set `Fin 2 × Fin 2` (the computational basis `|ij⟩`).  The identification with
the algebraic tensor product `ℂ² ⊗[ℂ] ℂ²` is given by `QC.tensorEquiv` below. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Coordinates of the four Bell states in the computational basis, before normalization. -/
def bellRaw : Fin 4 → (Fin 2 × Fin 2) → ℂ :=
  ![fun p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0,
    fun p => if p = (0, 0) then 1 else if p = (1, 1) then -1 else 0,
    fun p => if p = (0, 1) then 1 else if p = (1, 0) then 1 else 0,
    fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0]

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell (k : Fin 4) : TwoQubit :=
  WithLp.toLp 2 (fun p => ((Real.sqrt 2 : ℂ))⁻¹ * bellRaw k p)

lemma bell_apply (k : Fin 4) (p : Fin 2 × Fin 2) :
    bell k p = ((Real.sqrt 2 : ℂ))⁻¹ * bellRaw k p := rfl

lemma inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    have h' : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h'
  rw [← mul_inv, h]
  norm_num

/-! ## Orthonormality and completeness -/

/-- The Bell states form an orthonormal family. -/
lemma bell_orthonormal_family : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bell_apply, bellRaw,
    map_mul, map_inv₀, Complex.conj_ofReal]
  fin_cases k <;> fin_cases l <;> norm_num <;> rw [inv_sqrt_two_mul_self] <;> norm_num

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`:**
they are an orthonormal family and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  refine ⟨bell_orthonormal_family, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by simp
  have hspan := (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family hcard).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank] at hspan

/-- The Bell states packaged as an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  OrthonormalBasis.mk bell_orthonormal_family bell_orthonormal.2.ge

@[simp] lemma bellBasis_apply (k : Fin 4) : bellBasis k = bell k :=
  congrFun (OrthonormalBasis.coe_mk _ _) k

/-! ## Identification with the tensor product `ℂ² ⊗[ℂ] ℂ²` -/

/-- The computational basis `|0⟩, |1⟩` of a single qubit. -/
noncomputable def ket (i : Fin 2) : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single i 1

noncomputable def qbasis : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis

noncomputable def tqbasis : Module.Basis (Fin 2 × Fin 2) ℂ TwoQubit :=
  (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℂ).toBasis

lemma qbasis_apply (i : Fin 2) : qbasis i = ket i := by
  simp only [ket]
  simp [qbasis, EuclideanSpace.basisFun]
  rfl

lemma tqbasis_apply (p : Fin 2 × Fin 2) : tqbasis p = EuclideanSpace.single p (1 : ℂ) := by
  simp [tqbasis, EuclideanSpace.basisFun]
  rfl

/-- The canonical identification of the algebraic tensor product `ℂ² ⊗[ℂ] ℂ²` with the
coordinate model `TwoQubit`, sending `|i⟩ ⊗ |j⟩` to `|ij⟩`. -/
noncomputable def tensorEquiv :
    (EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] (EuclideanSpace ℂ (Fin 2)) ≃ₗ[ℂ] TwoQubit :=
  (qbasis.tensorProduct qbasis).equiv tqbasis (Equiv.refl _)

@[simp] lemma tensorEquiv_ket (i j : Fin 2) :
    tensorEquiv (ket i ⊗ₜ ket j) = EuclideanSpace.single (i, j) (1 : ℂ) := by
  rw [← qbasis_apply i, ← qbasis_apply j, ← tqbasis_apply (i, j),
    ← Module.Basis.tensorProduct_apply, tensorEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

lemma bell_zero : bell 0 =
    tensorEquiv (((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ ket 0 + ket 1 ⊗ₜ ket 1)) := by
  rw [map_smul, map_add, tensorEquiv_ket, tensorEquiv_ket]
  ext p
  fin_cases p <;> simp [bell_apply, bellRaw, EuclideanSpace.single_apply, Prod.ext_iff]

lemma bell_one : bell 1 =
    tensorEquiv (((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ ket 0 - ket 1 ⊗ₜ ket 1)) := by
  rw [map_smul, map_sub, tensorEquiv_ket, tensorEquiv_ket]
  ext p
  fin_cases p <;> simp [bell_apply, bellRaw, EuclideanSpace.single_apply, Prod.ext_iff]

lemma bell_two : bell 2 =
    tensorEquiv (((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ ket 1 + ket 1 ⊗ₜ ket 0)) := by
  rw [map_smul, map_add, tensorEquiv_ket, tensorEquiv_ket]
  ext p
  fin_cases p <;> simp [bell_apply, bellRaw, EuclideanSpace.single_apply, Prod.ext_iff]

lemma bell_three : bell 3 =
    tensorEquiv (((Real.sqrt 2 : ℂ))⁻¹ • (ket 0 ⊗ₜ ket 1 - ket 1 ⊗ₜ ket 0)) := by
  rw [map_smul, map_sub, tensorEquiv_ket, tensorEquiv_ket]
  ext p
  fin_cases p <;> simp [bell_apply, bellRaw, EuclideanSpace.single_apply, Prod.ext_iff]

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

