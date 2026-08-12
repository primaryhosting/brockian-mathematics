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

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realised concretely as the Hilbert space
of functions `Fin 2 × Fin 2 → ℂ` with the standard inner product. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Unnormalised coefficients of the four Bell states in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`. -/
def bellCoeff : Fin 4 → Fin 2 × Fin 2 → ℂ
  | 0, (0, 0) => 1
  | 0, (1, 1) => 1
  | 1, (0, 0) => 1
  | 1, (1, 1) => -1
  | 2, (0, 1) => 1
  | 2, (1, 0) => 1
  | 3, (0, 1) => 1
  | 3, (1, 0) => -1
  | _, _ => 0

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell (k : Fin 4) : TwoQubit :=
  (WithLp.equiv 2 _).symm fun p => (Real.sqrt 2 : ℂ)⁻¹ * bellCoeff k p

lemma bell_apply (k : Fin 4) (p : Fin 2 × Fin 2) :
    bell k p = (Real.sqrt 2 : ℂ)⁻¹ * bellCoeff k p := rfl

private lemma sq_sqrt_two : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this

/-- The Bell states are pairwise orthogonal unit vectors. -/
theorem bell_inner (k l : Fin 4) :
    (inner ℂ (bell k) (bell l) : ℂ) = if k = l then 1 else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, RCLike.inner_apply, bell_apply, map_mul, map_inv₀,
    Complex.conj_ofReal]
  set c : ℂ := (Real.sqrt 2 : ℂ)⁻¹ with hc
  have hcc : c * c = 1 / 2 := by
    rw [hc, ← mul_inv, sq_sqrt_two]
    norm_num
  fin_cases k <;> fin_cases l <;>
    norm_num [bellCoeff] <;>
    linear_combination (2 : ℂ) * hcc

theorem bell_orthonormal_family : Orthonormal ℂ bell := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa using bell_inner i j

/-- The two-qubit space is four dimensional. -/
lemma finrank_twoQubit : Module.finrank ℂ TwoQubit = 4 := by
  simp [finrank_euclideanSpace]

private lemma card_eq_finrank : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
  rw [finrank_twoQubit, Fintype.card_fin]

/-- The Bell states, packaged as an orthonormal basis of `ℂ² ⊗ ℂ²`. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family
    card_eq_finrank).toOrthonormalBasis (by simpa using bell_orthonormal_family)

@[simp] lemma coe_bellBasis : ⇑bellBasis = bell := by
  simp [bellBasis]

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`**: they are an
orthonormal family and they span the whole space. -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ ∧
      ∃ b : OrthonormalBasis (Fin 4) ℂ TwoQubit, ⇑b = bell :=
  ⟨bell_orthonormal_family, by
    have h := (basisOfOrthonormalOfCardEqFinrank bell_orthonormal_family
      card_eq_finrank).span_eq
    rwa [coe_basisOfOrthonormalOfCardEqFinrank] at h,
    bellBasis, coe_bellBasis⟩

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

