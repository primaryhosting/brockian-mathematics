/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped ComplexOrder

namespace Brockian

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `i`-th singular value of a complex square matrix `A`: the square root of the `i`-th
eigenvalue of the positive semidefinite matrix `Aᴴ * A`. -/

lemma norm_dotProduct_le (a b : n → ℂ) :
    ‖star a ⬝ᵥ b‖ ≤ ‖(WithLp.toLp 2 a : EuclideanSpace ℂ n)‖ *
      ‖(WithLp.toLp 2 b : EuclideanSpace ℂ n)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ n) (WithLp.toLp 2 b)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

/-- Each diagonal entry of `A` in the eigenbasis of `Aᴴ A` is bounded by the corresponding
singular value. -/
