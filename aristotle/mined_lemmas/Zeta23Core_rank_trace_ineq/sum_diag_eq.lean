/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix RCLike Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/

lemma sum_diag_eq {E ι κ : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (L : E →ₗ[𝕜] E)
    (f : OrthonormalBasis ι 𝕜 E) (g : OrthonormalBasis κ 𝕜 E) :
    ∑ i, inner 𝕜 (f i) (L (f i)) = ∑ j, inner 𝕜 (g j) (L (g j)) := by
  have h1 : ∀ i, inner 𝕜 (f i) (L (f i)) = ∑ j, inner 𝕜 (f i) (g j) * inner 𝕜 (g j) (L (f i)) :=
    fun i => (g.sum_inner_mul_inner (f i) (L (f i))).symm
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : ∀ i, inner 𝕜 (f i) (g j) * inner 𝕜 (g j) (L (f i))
      = inner 𝕜 ((LinearMap.adjoint L) (g j)) (f i) * inner 𝕜 (f i) (g j) := by
    intro i
    rw [LinearMap.adjoint_inner_left]
    ring
  simp_rw [h2]
  rw [f.sum_inner_mul_inner, LinearMap.adjoint_inner_left]

/-- The quadratic form of a matrix in terms of the inner product on `EuclideanSpace`. -/
