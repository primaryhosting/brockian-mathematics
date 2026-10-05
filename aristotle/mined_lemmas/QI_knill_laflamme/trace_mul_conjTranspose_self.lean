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

lemma trace_mul_conjTranspose_self (v : Matrix m (Fin 1) ℂ) :
    (v * vᴴ).trace = (fro v : ℂ) := by
  rw [Matrix.trace_mul_comm, trace_conjTranspose_mul_self]

/-- If a sum of rank-one positive matrices `u k * (u k)ᴴ` equals the rank-one matrix
`v * vᴴ`, then every `u k` is a scalar multiple of `v`. -/
