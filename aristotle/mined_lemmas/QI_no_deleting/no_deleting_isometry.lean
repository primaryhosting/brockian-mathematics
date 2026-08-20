import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QI

/-- A single qubit: the two-dimensional complex Hilbert space `ℂ²`. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- Two qubits: the Hilbert space `ℂ² ⊗ ℂ² ≃ ℂ^(2×2)`. -/
abbrev TwoQubits : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor (Kronecker) product of two qubit states. -/

theorem no_deleting_isometry :
    ¬ ∃ (U : TwoQubits →ₗᵢ[ℂ] TwoQubits) (blank : Qubit),
        ∀ ψ : Qubit, ‖ψ‖ = 1 → U (kron ψ ψ) = kron ψ blank := by
  rintro ⟨U, blank, hU⟩
  -- `U` preserves inner products, so `⟪ψ, φ⟫² = ⟪ψ, φ⟫ * ‖blank‖²` for unit vectors `ψ, φ`.
  have key : ∀ ψ φ : Qubit, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      ⟪ψ, φ⟫_ℂ * ⟪ψ, φ⟫_ℂ = ⟪ψ, φ⟫_ℂ * ⟪blank, blank⟫_ℂ := by
    intro ψ φ hψ hφ
    have h := U.inner_map_map (kron ψ ψ) (kron φ φ)
    rw [hU ψ hψ, hU φ hφ, inner_kron_kron, inner_kron_kron] at h
    exact h.symm
  -- Taking `ψ = φ = |0⟩` forces `‖blank‖ = 1`.
  have h1 : ⟪blank, blank⟫_ℂ = 1 := by
    have h := key ket0 ket0 norm_ket0 norm_ket0
    have hnorm : ⟪ket0, ket0⟫_ℂ = 1 := by
      rw [PiLp.inner_apply]
      simp [ket0, Fin.sum_univ_two]
    rw [hnorm, one_mul, one_mul] at h
    exact h.symm
  -- Taking `ψ = |0⟩`, `φ = (3/5)|0⟩ + (4/5)|1⟩` gives `(3/5)² = 3/5`, a contradiction.
  have h2 := key ket0 ketS norm_ket0 norm_ketS
  rw [inner_ket0_ketS, h1, mul_one] at h2
  norm_num at h2

/-- **No-deleting theorem.**  There is no unitary operator `U` on two qubits and no fixed
"blank" state `blank` with `U (|ψ⟩ ⊗ |ψ⟩) = |ψ⟩ ⊗ |blank⟩` for every unit vector `|ψ⟩`:
an unknown quantum state cannot be deleted. -/
