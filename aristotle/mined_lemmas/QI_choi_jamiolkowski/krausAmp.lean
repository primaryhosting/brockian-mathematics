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

def krausAmp (κ : Type) [DecidableEq κ] (K : Matrix m n ℂ) : Matrix (κ × m) (κ × n) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 then K x.2 y.2 else 0

/-- The (unnormalised) maximally entangled state `|ω⟩⟨ω|` with `|ω⟩ = ∑ i, eᵢ ⊗ eᵢ`. -/
