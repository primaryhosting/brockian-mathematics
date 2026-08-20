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

theorem norm_mulVec_congr {M : Matrix n m ℂ} {P : Matrix k m ℂ} (h : Mᴴ * M = Pᴴ * P)
    (x : m → ℂ) : ‖evec (M *ᵥ x)‖ = ‖evec (P *ᵥ x)‖ := by
  have h2 : ‖evec (M *ᵥ x)‖ ^ 2 = ‖evec (P *ᵥ x)‖ ^ 2 := by
    rw [normSq_mulVec, normSq_mulVec, h]
  nlinarith [norm_nonneg (evec (M *ᵥ x)), norm_nonneg (evec (P *ᵥ x))]

/-- A matrix viewed as a vector of `EuclideanSpace` indexed by pairs; its norm is the
Frobenius (Hilbert–Schmidt) norm. -/
