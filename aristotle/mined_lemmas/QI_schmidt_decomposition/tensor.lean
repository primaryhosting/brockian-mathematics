import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/

noncomputable def tensor (a : EuclideanSpace ℂ (Fin m)) (b : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin m × Fin n) :=
  WithLp.toLp 2 fun p => a p.1 * b p.2

