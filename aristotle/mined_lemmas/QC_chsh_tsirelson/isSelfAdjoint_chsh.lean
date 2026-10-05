/-
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QC

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, a self-adjoint element `a` bounded above by `r` and below by `-r`
(in the C⋆-order) has norm at most `r`. -/

theorem isSelfAdjoint_chsh {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsSelfAdjoint (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) := by
  unfold IsSelfAdjoint
  simp only [star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

/-- **Tsirelson's bound.** For a CHSH tuple `(A₀, A₁, B₀, B₁)` in a unital C⋆-algebra
(four ±1-valued observables, the `Aᵢ` commuting with the `Bⱼ`), the CHSH operator
`A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` has operator norm at most `2√2`. -/
