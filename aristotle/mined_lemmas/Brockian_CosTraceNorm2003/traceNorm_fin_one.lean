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

lemma traceNorm_fin_one (z : ℂ) : traceNorm (!![z] : Matrix (Fin 1) (Fin 1) ℂ) = ‖z‖ := by
  have hsq := sum_singularValue_sq (!![z] : Matrix (Fin 1) (Fin 1) ℂ)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hsq
  have h0 : singularValue (!![z] : Matrix (Fin 1) (Fin 1) ℂ) 0 ^ 2 = ‖z‖ ^ 2 := by
    simpa using hsq
  have := abs_eq_abs.2 (Or.inl (pow_left_injective (by norm_num) (by norm_num) ?_))
  · exact this
  · exact h0

/-- **Cos trace norm bound (2003).**  For every complex square matrix `A` and every phase `θ`,
the real part of `e^{iθ} · tr A`, namely `cos θ · Re(tr A) - sin θ · Im(tr A)`, is bounded above
by the trace norm (nuclear norm) `‖A‖₁ = ∑ σᵢ(A)`.  Taking the supremum over `θ` recovers the
sharp bound `|tr A| ≤ ‖A‖₁`. -/
