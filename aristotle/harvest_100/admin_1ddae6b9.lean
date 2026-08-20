/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- **Auxiliary computation.**  For symmetric operators `X`, `P` on a complex inner product
space and a unit vector `ψ` satisfying the canonical commutation relation
`X (P ψ) - P (X ψ) = i ℏ ψ`, the "centred" vectors
`u = X ψ - ⟨X⟩ ψ` and `v = P ψ - ⟨P⟩ ψ` satisfy `⟪u, v⟫ - ⟪v, u⟫ = i ℏ`. -/
theorem inner_comm_diff_of_canonical_commutator
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (X P : V →ₗ[ℂ] V)
    (hX : ∀ u v : V, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : V, inner ℂ (P u) v = inner ℂ u (P v))
    (ψ : V) (hψ : ‖ψ‖ = 1) (ℏ : ℝ)
    (hcomm : X (P ψ) - P (X ψ) = ((ℏ : ℂ) * Complex.I) • ψ) :
    inner ℂ (X ψ - (inner ℂ ψ (X ψ) : ℂ) • ψ) (P ψ - (inner ℂ ψ (P ψ) : ℂ) • ψ)
      - inner ℂ (P ψ - (inner ℂ ψ (P ψ) : ℂ) • ψ) (X ψ - (inner ℂ ψ (X ψ) : ℂ) • ψ)
      = (ℏ : ℂ) * Complex.I := by
  set a : ℂ := inner ℂ ψ (X ψ) with ha
  set b : ℂ := inner ℂ ψ (P ψ) with hb
  have hψψ : (inner ℂ ψ ψ : ℂ) = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    rw [this, hψ]
    norm_num
  have hXψψ : (inner ℂ (X ψ) ψ : ℂ) = a := by rw [hX, ha]
  have hPψψ : (inner ℂ (P ψ) ψ : ℂ) = b := by rw [hP, hb]
  have hmain : (inner ℂ (X ψ) (P ψ) : ℂ) - inner ℂ (P ψ) (X ψ) = (ℏ : ℂ) * Complex.I := by
    have h1 : (inner ℂ (X ψ) (P ψ) : ℂ) = inner ℂ ψ (X (P ψ)) := by rw [hX]
    have h2 : (inner ℂ (P ψ) (X ψ) : ℂ) = inner ℂ ψ (P (X ψ)) := by rw [hP]
    rw [h1, h2, ← inner_sub_right, hcomm, inner_smul_right, hψψ, mul_one]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hXψψ, hPψψ, hψψ, ha, hb]
  linear_combination hmain

/-- **Heisenberg uncertainty principle.**

Let `X` and `P` be symmetric (self-adjoint) operators on a complex inner product space `V`,
and let `ψ` be a normalized state satisfying the canonical commutation relation
`X (P ψ) - P (X ψ) = i ℏ ψ`.  Then the product of the standard deviations
`Δx = ‖X ψ - ⟨X⟩ ψ‖` and `Δp = ‖P ψ - ⟨P⟩ ψ‖` is at least `ℏ / 2`.

The proof combines the commutator identity with the Cauchy–Schwarz inequality
(`norm_inner_le_norm` in Mathlib). -/
theorem heisenberg_uncertainty
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (X P : V →ₗ[ℂ] V)
    (hX : ∀ u v : V, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : V, inner ℂ (P u) v = inner ℂ u (P v))
    (ψ : V) (hψ : ‖ψ‖ = 1) (ℏ : ℝ)
    (hcomm : X (P ψ) - P (X ψ) = ((ℏ : ℂ) * Complex.I) • ψ) :
    ℏ / 2 ≤ ‖X ψ - (inner ℂ ψ (X ψ) : ℂ) • ψ‖ * ‖P ψ - (inner ℂ ψ (P ψ) : ℂ) • ψ‖ := by
  set u : V := X ψ - (inner ℂ ψ (X ψ) : ℂ) • ψ with hu
  set v : V := P ψ - (inner ℂ ψ (P ψ) : ℂ) • ψ with hv
  have key : (inner ℂ u v : ℂ) - inner ℂ v u = (ℏ : ℂ) * Complex.I :=
    inner_comm_diff_of_canonical_commutator X P hX hP ψ hψ ℏ hcomm
  have h1 : |ℏ| = ‖(inner ℂ u v : ℂ) - inner ℂ v u‖ := by
    rw [key, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(inner ℂ u v : ℂ) - inner ℂ v u‖ ≤ ‖(inner ℂ u v : ℂ)‖ + ‖(inner ℂ v u : ℂ)‖ :=
    norm_sub_le _ _
  have h3 : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have h4 : ‖(inner ℂ v u : ℂ)‖ ≤ ‖v‖ * ‖u‖ := norm_inner_le_norm v u
  have h5 : |ℏ| ≤ 2 * (‖u‖ * ‖v‖) := by
    rw [h1]
    nlinarith [h2, h3, h4, mul_comm ‖u‖ ‖v‖]
  have h6 : ℏ ≤ |ℏ| := le_abs_self ℏ
  linarith

end QPhys

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

