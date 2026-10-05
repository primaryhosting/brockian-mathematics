import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexConjugate
open Matrix

namespace QI

section Frobenius

variable {m n : Type} [Fintype m] [Fintype n]

/-- The squared Frobenius norm of a complex matrix, as a real number. -/

lemma col_mul_one_by_one (v : Matrix m (Fin 1) ℂ) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    v * X = (X 0 0) • v := by
  ext i j
  fin_cases j
  simp [Matrix.mul_apply]
  ring

