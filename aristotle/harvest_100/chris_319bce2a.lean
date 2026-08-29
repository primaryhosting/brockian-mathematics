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

/-!
## Overview

The no-deleting theorem states that, given two copies of an unknown quantum state,
there is no unitary evolution that deletes one of the copies (sending it to a fixed
"blank" state) while leaving the ancilla in a fixed final state.

We model a qubit by `EuclideanSpace ℂ (Fin 2)`, an ancilla by `EuclideanSpace ℂ α`
for an arbitrary finite index type `α`, and the tensor product of state vectors by
`QI.tens` (the Kronecker product of coordinate vectors, which is the standard
concrete model of the tensor product of finite-dimensional Hilbert spaces).

A unitary is modelled as a `ℂ`-linear isometric equivalence `U`.  The key facts used
are that `U` preserves inner products and that the inner product is multiplicative
with respect to `tens`.
-/

namespace QI

open scoped ComplexConjugate

/-- The Kronecker (tensor) product of two finite-dimensional state vectors. -/
noncomputable def tens {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun p => a.ofLp p.1 * b.ofLp p.2

/-- The inner product is multiplicative with respect to the tensor product. -/
theorem inner_tens {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a c : EuclideanSpace ℂ ι) (b d : EuclideanSpace ℂ κ) :
    inner ℂ (tens a b) (tens c d) = inner ℂ a c * inner ℂ b d := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [tens, RCLike.inner_apply, map_mul]
  ring

/-- For a unit vector `x`, `⟪x, x⟫ = 1`. -/
theorem inner_self_of_norm_one {ι : Type*} [Fintype ι] {x : EuclideanSpace ℂ ι}
    (hx : ‖x‖ = 1) : inner ℂ x x = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hx]
  norm_num

/-- The first computational basis state of a qubit. -/
noncomputable def ket0 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The uniform superposition state `(|0⟩ + |1⟩)/√2`. -/
noncomputable def ketPlus : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem norm_ket0 : ‖ket0‖ = 1 := by
  simp [ket0]

theorem norm_ketPlus : ‖ketPlus‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ketPlus]

theorem inner_ket0_ketPlus : inner ℂ ket0 ketPlus = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [ket0, ketPlus, EuclideanSpace.inner_single_left]

/-- The two states `|0⟩` and `|+⟩` are neither equal nor orthogonal:
their overlap `c` satisfies `c ^ 2 ≠ c`. -/
theorem inner_ket0_ketPlus_sq_ne : inner ℂ ket0 ketPlus * inner ℂ ket0 ketPlus
    ≠ inner ℂ ket0 ketPlus := by
  rw [inner_ket0_ketPlus]
  intro h
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2)⁻¹ := by exact_mod_cast h
  have hr' : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 * (Real.sqrt 2)⁻¹ := by
    rw [one_mul]; exact hr
  have h1 : (Real.sqrt 2)⁻¹ = 1 := mul_right_cancel₀ (inv_ne_zero h2.ne') hr'
  have h3 : Real.sqrt 2 = 1 := by field_simp at h1; exact h1.symm
  have h4 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [h3] at h4
  norm_num at h4

/-- **No-deleting theorem.**  Let `blank` be a fixed blank qubit state, `anc` a fixed
initial ancilla state and `out` a fixed final ancilla state (all unit vectors).  There is
no unitary `U` on `qubit ⊗ qubit ⊗ ancilla` that maps `|ψ⟩ ⊗ |ψ⟩ ⊗ |anc⟩` to
`|ψ⟩ ⊗ |blank⟩ ⊗ |out⟩` for every unknown (unit) qubit state `ψ`: i.e. no unitary can
delete one of two copies of an unknown quantum state. -/
theorem no_deleting {α : Type*} [Fintype α]
    (blank : EuclideanSpace ℂ (Fin 2)) (anc out : EuclideanSpace ℂ α)
    (hblank : ‖blank‖ = 1) (hanc : ‖anc‖ = 1) (hout : ‖out‖ = 1)
    (U : EuclideanSpace ℂ (Fin 2 × Fin 2 × α) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2 × α)) :
    ¬ ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 →
        U (tens ψ (tens ψ anc)) = tens ψ (tens blank out) := by
  intro hU
  -- Unitarity forces the overlap `c = ⟪ψ, φ⟫` to satisfy `c * c = c` for all unit `ψ, φ`.
  have key : ∀ ψ φ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → ‖φ‖ = 1 →
      inner ℂ ψ φ * inner ℂ ψ φ = inner ℂ ψ φ := by
    intro ψ φ hψ hφ
    have h := U.inner_map_map (tens ψ (tens ψ anc)) (tens φ (tens φ anc))
    rw [hU ψ hψ, hU φ hφ, inner_tens, inner_tens, inner_tens, inner_tens,
      inner_self_of_norm_one hanc, inner_self_of_norm_one hblank,
      inner_self_of_norm_one hout] at h
    simpa using h.symm
  exact inner_ket0_ketPlus_sq_ne (key ket0 ketPlus norm_ket0 norm_ketPlus)

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

