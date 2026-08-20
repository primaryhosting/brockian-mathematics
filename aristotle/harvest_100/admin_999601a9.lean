import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realized as the Hilbert space of
functions `Fin 2 × Fin 2 → ℂ` with the standard inner product. -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- `1/√2`, the normalization constant of the Bell states. -/
noncomputable def invSqrt2 : ℂ := (Real.sqrt 2 : ℝ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at this
    norm_num at this
  field_simp [invSqrt2]
  linear_combination this

lemma conj_invSqrt2 : conj invSqrt2 = invSqrt2 := by
  simp [invSqrt2, Complex.conj_ofReal]

/-- Coefficient matrices of the four Bell states in the computational basis
`|ij⟩`, with rows indexed by the first qubit and columns by the second:
`Φ⁺, Φ⁻, Ψ⁺, Ψ⁻`. -/
noncomputable def bellMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![ !![invSqrt2, 0; 0, invSqrt2],
     !![invSqrt2, 0; 0, -invSqrt2],
     !![0, invSqrt2; invSqrt2, 0],
     !![0, invSqrt2; -invSqrt2, 0] ]

/-- The four Bell states
`(|00⟩ ± |11⟩)/√2` and `(|01⟩ ± |10⟩)/√2` as vectors of `ℂ² ⊗ ℂ²`. -/
noncomputable def bell (k : Fin 4) : Qubit2 :=
  WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => bellMatrix k p.1 p.2)

lemma bell_apply (k : Fin 4) (p : Fin 2 × Fin 2) :
    (bell k).ofLp p = bellMatrix k p.1 p.2 := rfl

lemma bell_inner (i j : Fin 4) :
    inner ℂ (bell i) (bell j)
      = ∑ p : Fin 2 × Fin 2, conj (bellMatrix i p.1 p.2) * bellMatrix j p.1 p.2 := by
  rw [PiLp.inner_apply]
  simp [bell_apply, RCLike.inner_apply]

/-- The four Bell states are orthonormal. -/
theorem bell_orthonormal_family : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [bell_inner]
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, bellMatrix, conj_invSqrt2,
      invSqrt2_mul_self] <;>
    ring_nf <;>
    norm_num [invSqrt2_mul_self]

/-- The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`:
they are orthonormal and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  refine ⟨bell_orthonormal_family, ?_⟩
  have hli : LinearIndependent ℂ bell := bell_orthonormal_family.linearIndependent
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ Qubit2 := by simp
  have := (basisOfLinearIndependentOfCardEqFinrank hli hcard).span_eq
  simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using this

/-- The Bell states packaged as an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ Qubit2 :=
  OrthonormalBasis.mk bell_orthonormal.1 (by rw [bell_orthonormal.2])

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

