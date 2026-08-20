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

theorem re_inner_apply_eq_sum_eigenvalues (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (ψ : E) :
    RCLike.re (inner ℂ ψ (H ψ)) =
      ∑ i, hH.eigenvalues hn i * ‖(hH.eigenvectorBasis hn).repr ψ i‖ ^ 2 := by
  have h1 : inner ℂ ψ (H ψ) = inner ℂ ((hH.eigenvectorBasis hn).repr ψ)
      ((hH.eigenvectorBasis hn).repr (H ψ)) :=
    ((hH.eigenvectorBasis hn).repr.inner_map_map ψ (H ψ)).symm
  rw [h1, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have key : ∀ (a : ℝ) (z : ℂ), RCLike.re ((a : ℂ) * z * conj z) = a * ‖z‖ ^ 2 := by
    intro a z
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [hH.eigenvectorBasis_apply_self_apply hn ψ i, RCLike.inner_apply]
  exact key _ _

/-- **Variational principle (Rayleigh–Ritz bound).**
Let `H` be a self-adjoint (symmetric) operator on a finite-dimensional complex inner product
space, and let `E₀` be a lower bound for its eigenvalues (the ground-state energy).  Then for
every nonzero state `ψ`, the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`. -/
