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

theorem isCHSHTuple_neg {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) : IsCHSHTuple (-A₀) (-A₁) B₀ B₁ where
  A₀_inv := by simpa using T.A₀_inv
  A₁_inv := by simpa using T.A₁_inv
  B₀_inv := T.B₀_inv
  B₁_inv := T.B₁_inv
  A₀_sa := by simp [T.A₀_sa]
  A₁_sa := by simp [T.A₁_sa]
  B₀_sa := T.B₀_sa
  B₁_sa := T.B₁_sa
  A₀B₀_commutes := by simp [T.A₀B₀_commutes]
  A₀B₁_commutes := by simp [T.A₀B₁_commutes]
  A₁B₀_commutes := by simp [T.A₁B₀_commutes]
  A₁B₁_commutes := by simp [T.A₁B₁_commutes]

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
