import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

theorem huckel_C18 :
    ((SimpleGraph.cycleGraph 18).adjMatrix ℂ).charpoly =
      ∏ k : Fin 18, (X - C ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)) := by
  have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr P_det_ne_zero
  let U : (Matrix (Fin 18) (Fin 18) ℂ)ˣ := Matrix.nonsingInvUnit P hunit
  have hUP : (U : Matrix (Fin 18) (Fin 18) ℂ) = P := rfl
  have hUinv : ((U⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) = P⁻¹ := rfl
  have hA : A = (U : Matrix (Fin 18) (Fin 18) ℂ) * Matrix.diagonal mu *
      ((U⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) := by
    rw [hUP, hUinv, ← A_mul_P, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  calc ((SimpleGraph.cycleGraph 18).adjMatrix ℂ).charpoly = A.charpoly := rfl
    _ = (Matrix.diagonal mu).charpoly := by rw [hA, Matrix.charpoly_units_conj]
    _ = ∏ k : Fin 18, (X - C (mu k)) := Matrix.charpoly_diagonal mu
    _ = _ := rfl

/-- The spectrum of the adjacency matrix of `C₁₈` is exactly the set of Hückel energies
`{2 cos (2πk/18) : k = 0, …, 17}`. -/
