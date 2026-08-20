import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a unitary matrix `W`, the matrix of squared norms of the entries of `W` is doubly
stochastic: its rows sum to `1` because `W * Wᴴ = 1`, and its columns sum to `1` because
`Wᴴ * W = 1`. -/

lemma re_trace_conj_diag {U V : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) (a b : n → ℝ) :
    RCLike.re (Matrix.trace ((U * Matrix.diagonal (RCLike.ofReal ∘ a) * star U) *
        (V * Matrix.diagonal (RCLike.ofReal ∘ b) * star V)))
      = ∑ j, ∑ k, a j * b k * ‖(star U * V) j k‖ ^ 2 := by
  set W : Matrix n n 𝕜 := star U * V with hWdef
  set Da : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ a) with hDa
  set Db : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ b) with hDb
  have hUU : U * star U = 1 := hU.2
  have hUU' : star U * U = 1 := hU.1
  have hstarW : star W = star V * U := by rw [hWdef, Matrix.star_mul, star_star]
  have hprod : (U * Da * star U) * (V * Db * star V) = U * (Da * W * Db * star W) * star U := by
    rw [hstarW, hWdef]
    simp only [← mul_assoc]
    rw [mul_assoc _ U (star U), hUU, mul_one]
  rw [hprod, Matrix.trace_mul_cycle, ← mul_assoc, hUU', one_mul]
  have hentry : Matrix.trace (Da * W * Db * star W)
      = ((∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDa, hDb]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, RCLike.star_def,
      Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hc : W j k * (starRingEnd 𝕜) (W j k) = ((‖W j k‖ : 𝕜)) ^ 2 := RCLike.mul_conj _
    linear_combination ((a j : 𝕜) * (b k : 𝕜)) * hc
  rw [hentry]
  simp

/-- **Von Neumann trace inequality**, Hermitian case: for Hermitian matrices `A`, `B` over an
`RCLike` field indexed by a finite type, `Re (tr (A * B))` is at most the sum of the products of
the eigenvalues of `A` and of `B`, each listed in decreasing order.

Here the decreasing enumeration of the eigenvalues is `Matrix.IsHermitian.eigenvalues₀`, which is
antitone by `Matrix.IsHermitian.eigenvalues₀_antitone`. -/
