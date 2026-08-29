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

lemma mul_colVec (A B : Matrix m m ℂ) (j : m) : A * colVec B j = colVec (A * B) j := by
  ext i x
  simp [colVec, Matrix.mul_apply]

