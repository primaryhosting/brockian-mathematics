/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/

def HasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix m n ℂ), ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ

/-- The amplification `id_κ ⊗ Φ`, acting on `κ`-indexed block matrices. -/
