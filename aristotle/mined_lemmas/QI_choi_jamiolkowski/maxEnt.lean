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

def maxEnt (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0

omit [Fintype m] [DecidableEq m] in
/-- **Key lemma**: a linear map between matrix algebras is completely determined by its
Choi matrix, via `Φ X a b = ∑ i j, X i j * C (i,a) (j,b)`. -/
