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

lemma fro_pos_of_projector {P : Matrix m m ℂ} (hP : IsCodeProjector P) : 0 < fro P := by
  rcases lt_or_eq_of_le (fro_nonneg P) with h | h
  · exact h
  · exact absurd ((fro_eq_zero_iff P).mp h.symm) hP.ne_zero

