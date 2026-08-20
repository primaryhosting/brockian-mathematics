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

theorem variational_bound (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ hH.eigenvalues hn i) {ψ : E} (hψ : ψ ≠ 0) :
    E₀ ≤ RCLike.re (inner ℂ ψ (H ψ)) / RCLike.re (inner ℂ ψ ψ) := by
  have hnorm : RCLike.re (inner ℂ ψ ψ) = ‖ψ‖ ^ 2 := inner_self_eq_norm_sq ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [hnorm, le_div_iff₀ hpos, re_inner_apply_eq_sum_eigenvalues hH hn ψ,
    norm_sq_eq_sum_eigencoords hH hn ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

omit [FiniteDimensional ℂ E] in
/-- The bound of `QPhys.variational_bound` is sharp: it is attained at a ground state,
i.e. at an eigenvector of `H` with eigenvalue `E₀`. -/
