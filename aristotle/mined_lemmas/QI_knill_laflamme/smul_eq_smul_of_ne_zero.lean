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

lemma smul_eq_smul_of_ne_zero {P : Matrix m m ℂ} (hP : P ≠ 0) {z w : ℂ}
    (h : z • P = w • P) : z = w := by
  by_contra hne
  apply hP
  have : (z - w) • P = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact h1

