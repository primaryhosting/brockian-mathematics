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

def krausAmp (k : Type) [DecidableEq k] (V : Matrix m n ℂ) : Matrix (k × m) (k × n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.2 q.2 else 0

omit [DecidableEq n] [DecidableEq m] in
/-- Collapsing the sums over `k × n` coming from a block-diagonal conjugation. -/
