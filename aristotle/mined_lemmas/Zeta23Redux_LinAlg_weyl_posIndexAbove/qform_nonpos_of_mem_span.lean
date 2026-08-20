/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real quadratic form `x ↦ ⟪x, M x⟫` attached to a matrix `M`. -/

lemma qform_nonpos_of_mem_span {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ
      (hM.eigenvectorBasis '' ((Finset.univ.filter fun i => hM.eigenvalues i ≤ 0) :
        Set (Fin d)))) :
    qform M x ≤ 0 := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter fun i => hM.eigenvalues i ≤ 0 with hs
  rw [qform_eq_sum hM]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ s
  · have h1 : hM.eigenvalues i ≤ 0 := by rw [hs] at hi; simpa using hi
    exact mul_nonpos_of_nonpos_of_nonneg h1 (by positivity)
  · rw [inner_eq_zero_of_mem_span hM hx hi]
    simp

/-- The span of a set of eigenvectors has dimension equal to the number of indices. -/
