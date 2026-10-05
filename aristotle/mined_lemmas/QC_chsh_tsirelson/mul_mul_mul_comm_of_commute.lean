import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [NormOneClass R]

/-- The CHSH operator associated to a CHSH tuple `(A₀, A₁, B₀, B₁)`. -/

theorem mul_mul_mul_comm_of_commute (x y z w : S) (h : y * z = z * y) :
    x * y * (z * w) = x * z * (y * w) := by
  calc x * y * (z * w) = x * (y * z * w) := by noncomm_ring
    _ = x * (z * y * w) := by rw [h]
    _ = x * z * (y * w) := by noncomm_ring

end Ring

/-- A self-adjoint involution in a unital C*-algebra has norm one. -/
