/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/

def HasKrausDecomposition (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (N : ℕ) (V : Fin N → Matrix m n ℂ), ∀ X, Φ X = ∑ a, V a * X * (V a)ᴴ

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Entrywise description of the conjugation `(V ⊗ 1) A (V ⊗ 1)ᴴ`. -/
