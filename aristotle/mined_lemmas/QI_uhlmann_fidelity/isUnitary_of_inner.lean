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

theorem isUnitary_of_inner [DecidableEq n] {U : Matrix n n ℂ}
    (h : ∀ x y : n → ℂ, star (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = star x ⬝ᵥ y) : Uᴴ * U = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  funext i
  have h1 := h (Pi.single i 1) y
  rw [dot_conjTranspose, Matrix.mulVec_mulVec] at h1
  simpa using h1

/-- Polar decomposition: every square matrix `M` factors as `U * √(Mᴴ M)` with `U` unitary. -/
