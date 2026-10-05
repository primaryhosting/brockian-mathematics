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

lemma norm_mulVec_evec (A : Matrix n n ℂ) (i : n) :
    ‖(WithLp.toLp 2 (A *ᵥ evec A i) : EuclideanSpace ℂ n)‖ = singularValue A i := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm, dotProduct_mulVec_evec_self,
    show RCLike.re ((singularValue A i ^ 2 : ℝ) : ℂ) = singularValue A i ^ 2 from
      Complex.ofReal_re _]
  exact Real.sqrt_sq (singularValue_nonneg A i)

