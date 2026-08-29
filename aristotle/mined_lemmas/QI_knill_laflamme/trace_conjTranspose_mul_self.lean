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

lemma trace_conjTranspose_mul_self (A : Matrix m n ℂ) :
    (Aᴴ * A).trace = (fro A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    fro, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

