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

def KnillLaflammeCondition (P : Matrix m m ℂ) (E : ι → Matrix m m ℂ) : Prop :=
  ∃ c : ι → ι → ℂ, ∀ a b, P * (E a)ᴴ * E b * P = c a b • P

/-- The code with projector `P` corrects the error channel whose Kraus operators are `E`:
there is a quantum channel (given by Kraus operators `R`) which restores every state
supported on the code. -/
