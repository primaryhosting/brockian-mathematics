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

section CStar

variable {𝔄 : Type*} [NormedRing 𝔄] [StarRing 𝔄] [CStarRing 𝔄]

/-- In a C⋆-ring the unit has norm at most one (it is `0` or `1`). -/

theorem norm_one_le : ‖(1 : 𝔄)‖ ≤ 1 := by
  have h : ‖(1 : 𝔄)‖ * ‖(1 : 𝔄)‖ = ‖(1 : 𝔄)‖ := by
    have := CStarRing.norm_star_mul_self (x := (1 : 𝔄))
    simpa using this.symm
  nlinarith [norm_nonneg (1 : 𝔄)]

/-- A self-adjoint involution in a C⋆-ring has norm at most one. -/
