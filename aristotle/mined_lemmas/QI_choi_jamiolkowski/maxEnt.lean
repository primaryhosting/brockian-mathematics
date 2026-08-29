import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped MatrixOrder ComplexOrder

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The ampliation `id_d ⊗ Φ` of a linear map `Φ` between matrix algebras, described
blockwise: the `(a, b)` block of the output is `Φ` applied to the `(a, b)` block of the input. -/

def maxEnt (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => (if p.1 = p.2 then 1 else 0) * (if q.1 = q.2 then 1 else 0)

