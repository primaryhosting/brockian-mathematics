/-
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open Polynomial Finset

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, given by
Whitney's rank generating formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`,
where `r` is the (natural-number valued) rank function of `M`. -/

theorem natAbs_coeff_X_sub_one_pow (n k : ℕ) :
    ((((X : Polynomial ℤ) - 1) ^ n).coeff k).natAbs = n.choose k := by
  have h : ((X : Polynomial ℤ) - 1) = X + C (-1) := by simp [sub_eq_add_neg]
  rw [h, coeff_X_add_C_pow]
  rcases Nat.even_or_odd (n - k) with h | h <;> simp [h.neg_one_pow]

/-- Log-concavity of the binomial coefficients: `C(n,k) * C(n,k+2) ≤ C(n,k+1)^2`. -/
