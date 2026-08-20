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

theorem norm_commutator_le {X Y : 𝔄} (hX : star X = X) (hXsq : X * X = 1)
    (hY : star Y = Y) (hYsq : Y * Y = 1) : ‖X * Y - Y * X‖ ≤ 2 := by
  have hx := norm_le_one_of_sa_involution hX hXsq
  have hy := norm_le_one_of_sa_involution hY hYsq
  have h1 : ‖X * Y‖ ≤ 1 := le_trans (norm_mul_le _ _) (by nlinarith [norm_nonneg X, norm_nonneg Y])
  have h2 : ‖Y * X‖ ≤ 1 := le_trans (norm_mul_le _ _) (by nlinarith [norm_nonneg X, norm_nonneg Y])
  calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- The square of the CHSH operator: `C ^ 2 = 4 - [A₀, A₁] [B₀, B₁]`. -/
