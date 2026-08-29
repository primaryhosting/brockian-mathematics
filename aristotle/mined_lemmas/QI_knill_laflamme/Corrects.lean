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

def Corrects (P : Matrix m m ℂ) (E : ι → Matrix m m ℂ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (R : κ → Matrix m m ℂ),
    (∑ k, (R k)ᴴ * R k = 1) ∧
      ∀ ρ : Matrix m m ℂ, P * ρ * P = ρ → ∑ k, ∑ a, (R k * E a) * ρ * (R k * E a)ᴴ = ρ

end Defs

section Columns

variable {m : Type} [Fintype m] [DecidableEq m]

/-- Multiplication of a column vector by a `1 × 1` matrix is scalar multiplication. -/
