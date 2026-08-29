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

lemma exists_colVec_ne_zero {A : Matrix m m ℂ} (hA : A ≠ 0) : ∃ j, colVec A j ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hA
  ext i j
  have := congrFun (congrFun (hc j) i) 0
  simpa [colVec] using this

/-- If a matrix acts as a scalar on every vector of the code space, it is a scalar multiple
of the code projector on that space. -/
