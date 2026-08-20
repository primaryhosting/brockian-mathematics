import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Isometries defined on the range of a linear map -/

section Isom

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- If `f` and `g` have the same norm pointwise, there is a linear isometry defined on the
range of `f` sending `f x` to `g x`. -/

theorem IsContr.fro_mul {Z : Matrix n n ℂ} (hZ : IsContr Z) (X : Matrix n m ℂ) :
    ‖fro (Z * X)‖ ≤ ‖fro X‖ := by
  have hcol : ∀ j : m, (fun i => (Z * X) i j) = Z *ᵥ (fun i => X i j) := by
    intro j
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hsq : ‖fro (Z * X)‖ ^ 2 ≤ ‖fro X‖ ^ 2 := by
    rw [normSq_fro_eq_sum_col, normSq_fro_eq_sum_col]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcol j]
    have h1 := hZ (fun i => X i j)
    nlinarith [norm_nonneg (evec (Z *ᵥ fun i => X i j)), norm_nonneg (evec fun i => X i j)]
  nlinarith [norm_nonneg (fro (Z * X)), norm_nonneg (fro X)]

/-! ### Polar decomposition and factorization of matrices -/

omit [Fintype n] in
