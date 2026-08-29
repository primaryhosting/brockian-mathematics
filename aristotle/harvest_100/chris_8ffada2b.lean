/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)` indexed by pairs of qubit values. -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p => if p = (0, 0) ∨ p = (1, 1) then (1 : ℂ) / Real.sqrt 2 else 0

/-- The coordinate definition of `ghz2` agrees with `(|00⟩ + |11⟩)/√2`, where `|ij⟩` is the
standard basis vector `EuclideanSpace.single (i, j) 1`. -/
theorem ghz2_eq_superposition : ghz2 = ((Real.sqrt 2 : ℂ))⁻¹ •
    (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)
      + EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2)) (1 : ℂ)) := by
  ext p
  by_cases h0 : p = (0, 0)
  · simp [ghz2, h0, EuclideanSpace.single_apply, Prod.ext_iff]
  · by_cases h1 : p = (1, 1)
    · simp [ghz2, h1, EuclideanSpace.single_apply, Prod.ext_iff]
    · simp only [ghz2, h0, h1, or_self, WithLp.ofLp_toLp, PiLp.smul_apply,
        PiLp.add_apply, EuclideanSpace.single_apply, smul_eq_mul]
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp_all [Prod.ext_iff]

/-- The 2-qubit GHZ state is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  have hsq : ‖(1 : ℂ) / (Real.sqrt 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [norm_div]
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hcoord : ∀ p : Fin 2 × Fin 2, ‖ghz2.ofLp p‖ ^ 2 =
      if p = (0, 0) ∨ p = (1, 1) then (1 / 2 : ℝ) else 0 := by
    intro p
    by_cases hp : p = (0, 0) ∨ p = (1, 1)
    · simp only [ghz2, if_pos hp, hsq]
    · simp [ghz2, hp]
  rw [EuclideanSpace.norm_eq]
  simp only [hcoord]
  rw [Fintype.sum_prod_type]
  norm_num [Fin.sum_univ_two, Prod.ext_iff]

end QC

