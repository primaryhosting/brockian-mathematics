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

theorem exists_isometry_extension [FiniteDimensional ℂ E] (f g : E →ₗ[ℂ] E)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : E →ₗᵢ[ℂ] E, ∀ x, U (f x) = g x := by
  obtain ⟨L, hL⟩ := exists_isometry_on_range f g h
  refine ⟨L.extend, fun x => ?_⟩
  have hx := L.extend_apply ⟨f x, LinearMap.mem_range_self f x⟩
  simpa [hL x] using hx

end Isom

/-! ### Euclidean vectors and the Frobenius (Hilbert–Schmidt) inner product -/

variable {n m k : Type} [Fintype n] [Fintype m] [Fintype k]

/-- A plain function viewed as a vector of `EuclideanSpace`. -/
