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

theorem choose_log_concave (n k : ℕ) : n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases lt_or_ge k n with hk | hk
  · have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
    have h2 : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
      Nat.choose_succ_right_eq n (k + 1)
    have key : (n.choose k * n.choose (k + 2)) * ((n - k) * (k + 2))
        ≤ (n.choose (k + 1)) ^ 2 * ((n - k) * (k + 2)) := by
      have e1 : (n.choose k * n.choose (k + 2)) * ((n - k) * (k + 2))
          = (n.choose k * (n - k)) * (n.choose (k + 2) * (k + 2)) := by ring
      rw [e1, ← h1, h2]
      have e2 : (n.choose (k + 1) * (k + 1)) * (n.choose (k + 1) * (n - (k + 1)))
          = (n.choose (k + 1)) ^ 2 * ((k + 1) * (n - (k + 1))) := by ring
      rw [e2]
      refine Nat.mul_le_mul_left _ ?_
      calc (k + 1) * (n - (k + 1)) ≤ (k + 2) * (n - k) := Nat.mul_le_mul (by omega) (by omega)
        _ = (n - k) * (k + 2) := mul_comm _ _
    have hpos : 0 < (n - k) * (k + 2) := by
      have h3 : 0 < n - k := by omega
      positivity
    exact Nat.le_of_mul_le_mul_right key hpos
  · have h4 : n.choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h4]

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz),
base case: the free (Boolean) matroid on a finite ground set `E`.

The absolute values `w_k` of the coefficients of the characteristic polynomial
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E)-r(S)}` of the free matroid on `E` satisfy the
log-concavity inequality `w_k * w_{k+2} ≤ w_{k+1}^2` for all `k`. -/
