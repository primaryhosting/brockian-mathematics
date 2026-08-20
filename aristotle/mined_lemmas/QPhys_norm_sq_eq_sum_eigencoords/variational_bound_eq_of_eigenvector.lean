import Mathlib
/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the requested header comment is placed immediately after `import Mathlib`.

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

namespace QPhys

open RCLike ComplexConjugate

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E}

/-- Parseval: the squared norm of `ψ` is the sum of the squared moduli of its
coordinates in an eigenvector basis of `H`. -/

theorem variational_bound_eq_of_eigenvector {E₀ : ℝ} {ψ : E} (hψ : ψ ≠ 0)
    (hHψ : H ψ = (E₀ : ℂ) • ψ) :
    RCLike.re (inner ℂ ψ (H ψ)) / RCLike.re (inner ℂ ψ ψ) = E₀ := by
  have hnorm : RCLike.re (inner ℂ ψ ψ) = ‖ψ‖ ^ 2 := inner_self_eq_norm_sq ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  have hnum : RCLike.re (inner ℂ ψ (H ψ)) = E₀ * ‖ψ‖ ^ 2 := by
    rw [hHψ, inner_smul_right]
    simp [← Complex.ofReal_pow]
  rw [hnum, hnorm, mul_div_assoc, div_self hpos.ne', mul_one]

end QPhys

