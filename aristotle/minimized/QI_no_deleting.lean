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

noncomputable def kron (ψ φ : Qubit) : TwoQubits :=
  WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => ψ.ofLp p.1 * φ.ofLp p.2)

/-- The inner product on the two-qubit space factorises on product states. -/

theorem inner_kron_kron (ψ φ ψ' φ' : Qubit) :
    ⟪kron ψ φ, kron ψ' φ'⟫_ℂ = ⟪ψ, ψ'⟫_ℂ * ⟪φ, φ'⟫_ℂ := by
  simp [kron, PiLp.inner_apply, Fintype.sum_prod_type]
  ring

/-- The computational basis state `|0⟩`. -/

noncomputable def ket0 : Qubit := WithLp.toLp 2 ![1, 0]

/-- The state `(3/5)|0⟩ + (4/5)|1⟩`, which is not orthogonal to `|0⟩`. -/

noncomputable def ketS : Qubit := WithLp.toLp 2 ![3 / 5, 4 / 5]

theorem norm_ket0 : ‖ket0‖ = 1 := by
  simp [ket0, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem norm_ketS : ‖ketS‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ketS, Fin.sum_univ_two]
  norm_num

theorem inner_ket0_ketS : ⟪ket0, ketS⟫_ℂ = 3 / 5 := by
  simp [ket0, ketS, PiLp.inner_apply, Fin.sum_univ_two]

/-- **No-deleting theorem** (strong form).  There is no linear isometry `U` of the two-qubit
space and no fixed "blank" state `blank` such that `U` maps `|ψ⟩ ⊗ |ψ⟩` to `|ψ⟩ ⊗ |blank⟩`
for every unit vector `|ψ⟩`; i.e. no machine can delete one of two copies of an unknown
quantum state. -/

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
