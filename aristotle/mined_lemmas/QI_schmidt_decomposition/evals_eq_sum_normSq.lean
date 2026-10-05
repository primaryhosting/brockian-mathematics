/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma evals_eq_sum_normSq (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j : Fin m) :
    evals ψ j = ∑ q, Complex.normSq (wcoef ψ j q) := by
  have h := wcoef_inner ψ j j
  rw [if_pos rfl] at h
  have h2 : ((∑ q, Complex.normSq (wcoef ψ j q) : ℝ) : ℂ) = (evals ψ j : ℂ) := by
    rw [← h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [Complex.normSq_eq_conj_mul_self]
  exact_mod_cast h2.symm

