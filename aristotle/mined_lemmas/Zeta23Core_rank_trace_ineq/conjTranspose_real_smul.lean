/-
/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Rank–trace inequality (preprint Lemma 3.2):
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P+Q‖_F²`,
for `P` positive semidefinite of rank at most `r`, `Q` Hermitian with at most `b` positive
eigenvalues, and `c > 0`.

The proof does not use von Neumann's trace inequality; instead it uses the two orthogonal
projections `Pi` (onto the positive spectral subspace of `Q`) and `R` (onto the range of the
compression `(1 - Pi) P (1 - Pi)`), and the elementary estimate `0 ≤ ‖S - M‖_F²` for
`S = P + Q` and `M = c·Pi + (c/2)·R`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Zeta23Core

open Matrix
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/

theorem conjTranspose_real_smul (a : ℝ) (A : Matrix n n 𝕜) : (a • A)ᴴ = a • Aᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, RCLike.real_smul_eq_coe_mul, RCLike.conj_ofReal]

/-! ## The core inequality, given a suitable pair of orthogonal projections -/

/-- The main estimate, assuming the existence of two orthogonal projections `Pi` (capturing the
positive part of `Q`) and `R` (capturing the part of the range of `P` orthogonal to `Pi`). -/
