/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the imports.)

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
open scoped TensorProduct

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

/-- The state space of a qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- **Key intermediate lemma.**  Suppose a unitary `U` on `(Qubit ⊗ Qubit) ⊗ A` implements
deletion, i.e. it maps `ψ ⊗ ψ ⊗ anc` to `ψ ⊗ blank ⊗ out` for every unit vector `ψ`, where the
blank state `blank` and the final ancilla state `out` do not depend on `ψ`.  Since `U` preserves
inner products, for all unit vectors `ψ, φ` we get `⟪ψ, φ⟫ ^ 2 = ⟪ψ, φ⟫`. -/
theorem inner_sq_eq_inner_of_deleting
    {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {anc out : A} {blank : Qubit}
    {U : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] A ≃ₗᵢ[ℂ] (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] A}
    (hanc : ‖anc‖ = 1)
    (hU : ∀ psi : Qubit, ‖psi‖ = 1 →
      U ((psi ⊗ₜ[ℂ] psi) ⊗ₜ[ℂ] anc) = (psi ⊗ₜ[ℂ] blank) ⊗ₜ[ℂ] out)
    {psi phi : Qubit} (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    (inner ℂ psi phi : ℂ) ^ 2 = inner ℂ psi phi := by
  -- Unitarity forces the blank state and the ancilla output to have product of norms `1`.
  have hnorm : ‖blank‖ * ‖out‖ = 1 := by
    have := congrArg norm (hU psi hpsi)
    rw [U.norm_map] at this
    simpa [TensorProduct.norm_tmul, hpsi, hanc] using this.symm
  have hinner : (inner ℂ (U ((psi ⊗ₜ[ℂ] psi) ⊗ₜ[ℂ] anc)) (U ((phi ⊗ₜ[ℂ] phi) ⊗ₜ[ℂ] anc)) : ℂ) =
      inner ℂ ((psi ⊗ₜ[ℂ] psi) ⊗ₜ[ℂ] anc) ((phi ⊗ₜ[ℂ] phi) ⊗ₜ[ℂ] anc) :=
    @LinearIsometryEquiv.inner_map_map ℂ ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] A) _ _ _
      ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] A) _ _ U _ _
  rw [hU psi hpsi, hU phi hphi] at hinner
  simp only [TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K] at hinner
  have hb : ((‖blank‖ : ℂ)) ^ 2 * ((‖out‖ : ℂ)) ^ 2 = 1 := by
    have : ((‖blank‖ * ‖out‖ : ℝ) : ℂ) = 1 := by rw [hnorm]; norm_num
    push_cast at this
    rw [← mul_pow, this, one_pow]
  -- restate `hinner` so that all its atoms are elaborated in the same way as in the goal
  have hinner2 : (inner ℂ psi phi : ℂ) * ((‖blank‖ : ℝ) : ℂ) ^ 2 * (((‖out‖ : ℝ)) : ℂ) ^ 2
      = (inner ℂ psi phi : ℂ) * (inner ℂ psi phi : ℂ) * (((‖anc‖ : ℝ)) : ℂ) ^ 2 := hinner
  rw [hanc] at hinner2
  push_cast at hinner2
  linear_combination -hinner2 + (inner ℂ psi phi : ℂ) * hb

/-- **No-deleting theorem.**  There is no unitary that deletes an unknown quantum state:
for any ancilla space `A`, any unit ancilla state `anc`, any fixed "blank" qubit state `blank`
and any fixed final ancilla state `out`, no unitary `U` on `(Qubit ⊗ Qubit) ⊗ A` can satisfy
`U (ψ ⊗ ψ ⊗ anc) = ψ ⊗ blank ⊗ out` for every unit vector `ψ`, i.e. no unitary can erase the
second of two identical copies of an arbitrary unknown qubit state. -/
theorem no_deleting
    {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (anc out : A) (blank : Qubit)
    (U : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] A ≃ₗᵢ[ℂ] (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] A)
    (hanc : ‖anc‖ = 1) :
    ¬ ∀ psi : Qubit, ‖psi‖ = 1 →
      U ((psi ⊗ₜ[ℂ] psi) ⊗ₜ[ℂ] anc) = (psi ⊗ₜ[ℂ] blank) ⊗ₜ[ℂ] out := by
  intro hU
  -- the computational basis vector `|0⟩` and the uniform superposition `|+⟩`
  set e0 : Qubit := EuclideanSpace.single (0 : Fin 2) (1 : ℂ) with he0
  set e1 : Qubit := EuclideanSpace.single (1 : Fin 2) (1 : ℂ) with he1
  set eplus : Qubit := ((Real.sqrt 2 : ℂ))⁻¹ • (e0 + e1) with heplus
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hne0 : ‖e0‖ = 1 := by simp [he0]
  have hneplus : ‖eplus‖ = 1 := by
    simp [heplus, he0, he1, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    norm_num
  have hip : (inner ℂ e0 eplus : ℂ) = ((Real.sqrt 2 : ℂ))⁻¹ := by
    simp [heplus, he0, he1, EuclideanSpace.inner_single_left]
  have key := inner_sq_eq_inner_of_deleting (U := U) hanc hU hne0 hneplus
  rw [hip] at key
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
  have hone : ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    field_simp at key
    linear_combination -key
  have hone' : Real.sqrt 2 = 1 := by exact_mod_cast hone
  have : (2 : ℝ) = 1 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [hone'] at this
    simpa using this.symm
  norm_num at this

end QI

