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

theorem normSq_fro (X : Matrix n m ℂ) : ((‖fro X‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * X).trace := by
  rw [← inner_fro X X, EuclideanSpace.inner_eq_star_dotProduct]
  have h : (‖fro X‖ ^ 2 : ℝ) = ∑ p : n × m, ‖X p.1 p.2‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rfl
  rw [h]
  push_cast
  simp [fro, dotProduct, ← Complex.mul_conj']

/-- Cauchy–Schwarz for the Frobenius inner product. -/
