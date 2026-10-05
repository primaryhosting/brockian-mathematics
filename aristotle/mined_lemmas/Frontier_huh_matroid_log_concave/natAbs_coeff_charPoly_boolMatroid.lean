import Mathlib

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

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace Frontier

/-- The rank of a finite set `S` in a matroid `M`, as a natural number. -/

lemma natAbs_coeff_charPoly_boolMatroid (n k : ℕ) :
    ((charPoly (boolMatroid n) univ).coeff k).natAbs = n.choose k := by
  have h : (X - 1 : ℤ[X]) = X + C (-1 : ℤ) := by simp [sub_eq_add_neg]
  rw [charPoly_boolMatroid, h, coeff_X_add_C_pow]
  rw [Int.natAbs_mul]
  rcases Nat.even_or_odd (n - k) with he | ho
  · rw [he.neg_one_pow]; simp
  · rw [ho.neg_one_pow]; simp

/-- Binomial coefficients form a log-concave sequence. -/
