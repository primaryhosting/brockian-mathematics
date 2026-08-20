import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

universe u

variable {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras, acting on
`k × n` block matrices: the `(x, y)` block of `M` (an `n × n` matrix) is sent to the
`(x, y)` block of the result (an `m × m` matrix). -/

def krausAmpl (B : Matrix (n × m) (n × m) ℂ) (r : n × m) (k : Type*) [DecidableEq k] :
    Matrix (k × m) (k × n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (starRingEnd ℂ) (B r (q.2, p.2)) else 0

omit [DecidableEq m] in
/-- Kraus-type decomposition of the amplification, given a factorization `choi Φ = Bᴴ * B`. -/
