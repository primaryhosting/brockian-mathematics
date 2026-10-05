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

lemma wcoef_eq_zero (ψ : EuclideanSpace ℂ (Fin m × Fin n)) {j : Fin m} (hj : evals ψ j = 0)
    (q : Fin n) : wcoef ψ j q = 0 := by
  rw [evals_eq_sum_normSq] at hj
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => Complex.normSq_nonneg (wcoef ψ j q))).mp hj q (Finset.mem_univ q)
  exact Complex.normSq_eq_zero.mp this

