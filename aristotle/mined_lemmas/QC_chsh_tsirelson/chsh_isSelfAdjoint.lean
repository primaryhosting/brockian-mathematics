/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace QC

/-- The square of the CHSH operator: `S² = 4 + [A₁, A₀] [B₀, B₁]`. -/

theorem chsh_isSelfAdjoint {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    star (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ := by
  simp only [star_add, star_sub, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

/-- A self-adjoint involution in a C*-algebra has norm at most one. -/
