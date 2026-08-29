import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/

def HasKrausRepresentation (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ V : n × m → Matrix m n ℂ, ∀ X, Φ X = ∑ c, V c * X * (V c)ᴴ

section Helpers

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
