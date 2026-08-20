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
