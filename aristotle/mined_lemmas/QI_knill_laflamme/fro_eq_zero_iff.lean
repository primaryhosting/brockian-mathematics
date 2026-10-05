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

lemma fro_eq_zero_iff (A : Matrix m n ℂ) : fro A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    unfold fro at h
    have h1 : ∀ i ∈ Finset.univ, (∑ j, ‖A i j‖ ^ 2) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h
      intro i _
      positivity
    have h2 := h1 i (Finset.mem_univ i)
    have h3 : ∀ j ∈ Finset.univ, ‖A i j‖ ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h2
      intro j _
      positivity
    have := h3 j (Finset.mem_univ j)
    simpa using this
  · intro h
    subst h
    simp [fro]

end Frobenius



section Defs

variable {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]

/-- `P` is the orthogonal projector onto a (nonzero) code subspace. -/
structure IsCodeProjector (P : Matrix m m ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for the code with projector `P` and the error
operators `E`: `P Eₐ† E_b P = c a b • P` for some matrix of scalars `c`. -/
