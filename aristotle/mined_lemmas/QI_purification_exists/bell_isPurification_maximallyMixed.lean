import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

theorem bell_isPurification_maximallyMixed :
    IsPurification ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptraceRight, pureDensity] <;>
    · field_simp
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

/-! ### The linear-algebraic core -/

/-- Two linear maps with the same pointwise norms differ by a linear isometry of the
target space. -/
