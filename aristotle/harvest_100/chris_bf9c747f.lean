/-
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The index type of computational basis states of a 3-qubit register. -/
abbrev Qubits3 := Fin 2 × Fin 2 × Fin 2

/-- The computational basis state `|q⟩` of a 3-qubit register, as a unit vector of the
Hilbert space `EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)`. -/
noncomputable def ket (q : Qubits3) : EuclideanSpace ℂ Qubits3 := EuclideanSpace.single q 1

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz3 : EuclideanSpace ℂ Qubits3 :=
  ((Real.sqrt 2)⁻¹ : ℝ) • (ket (0, 0, 0) + ket (1, 1, 1))

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a unit vector.

The key Mathlib ingredients are `EuclideanSpace.norm_single` (each basis ket has norm `1`),
`EuclideanSpace.inner_single_left` (the two kets are orthogonal) and the Pythagorean identity
`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  simp only [ghz3, ket]
  set v : EuclideanSpace ℂ Qubits3 :=
    EuclideanSpace.single (0, 0, 0) 1 + EuclideanSpace.single (1, 1, 1) 1 with hv
  have horth :
      inner ℂ (EuclideanSpace.single (0, 0, 0) (1 : ℂ) : EuclideanSpace ℂ Qubits3)
        (EuclideanSpace.single (1, 1, 1) (1 : ℂ)) = 0 := by
    simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, Prod.ext_iff]
  have hsq : ‖v‖ * ‖v‖ = 2 := by
    rw [hv, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
      EuclideanSpace.norm_single, EuclideanSpace.norm_single]
    norm_num
  have h2 : ‖v‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_mul_self (norm_nonneg v), hsq]
  rw [norm_smul, h2, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

end QC

