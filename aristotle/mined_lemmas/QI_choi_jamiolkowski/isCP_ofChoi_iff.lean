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

theorem isCP_ofChoi_iff (C : Matrix (n × m) (n × m) ℂ) :
    IsCP (ofChoi C) ↔ C.PosSemidef := by
  have h : choi (ofChoi C) = C := choiEquiv.apply_symm_apply C
  rw [choi_jamiolkowski, h]

/-- The transposition map on `n × n` matrices, as a `ℂ`-linear map. -/
