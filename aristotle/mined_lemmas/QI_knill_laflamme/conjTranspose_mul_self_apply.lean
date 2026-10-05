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

lemma conjTranspose_mul_self_apply (v : Matrix m (Fin 1) ℂ) :
    (vᴴ * v) 0 0 = (fro v : ℂ) := by
  have h := trace_conjTranspose_mul_self v
  simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_one] using h

