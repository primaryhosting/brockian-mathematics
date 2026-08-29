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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, in its
Whitney rank-generating form
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/

theorem whitney_freeOn (E : Finset α) (k : ℕ) :
    whitney (Matroid.freeOn (↑E : Set α)) E k = E.card.choose k := by
  have h : ((X : Polynomial ℤ) - 1) = X + C (-1 : ℤ) := by simp [sub_eq_add_neg]
  rw [whitney, charPoly_freeOn, h, coeff_X_add_C_pow]
  simp [Int.natAbs_mul, Int.natAbs_pow]

/-- **Adiprasito–Huh–Katz, base case.**  The coefficients of the characteristic polynomial
of a matroid form a log-concave sequence, verified here for the free (Boolean) matroid on
a finite ground set `E`: the absolute values of the coefficients of
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)} = (t-1)^{|E|}` satisfy
`|w_k| * |w_{k+2}| ≤ |w_{k+1}|^2`. -/
