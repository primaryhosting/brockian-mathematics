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

set_option grind.warning false

namespace Frontier

open Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

theorem coeff_charPoly_freeOn [Fintype α] (i : ℕ) :
    (charPoly (Matroid.freeOn (Set.univ : Set α))).coeff i
      = (-1) ^ (Fintype.card α - i) * ((Fintype.card α).choose i : ℤ) := by
  set n := Fintype.card α with hn
  rw [charPoly_freeOn, Polynomial.finset_sum_coeff]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (((n.choose k : Polynomial ℤ)) * (-1) ^ k * X ^ (n - k)).coeff i
        = if n - k = i then ((n.choose k : ℤ)) * (-1) ^ k else 0 := by
    intro k _
    have h : ((n.choose k : Polynomial ℤ)) * (-1) ^ k = C (((n.choose k : ℤ)) * (-1) ^ k) := by
      push_cast [Polynomial.C_mul, Polynomial.C_pow]
      simp
    rw [h, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [eq_comm]
  rw [Finset.sum_congr rfl hterm]
  by_cases hi : i ≤ n
  · rw [Finset.sum_eq_single (n - i)]
    · rw [if_pos (by omega), Nat.choose_symm hi]
      ring
    · intro k hk hne
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Finset.sum_eq_zero]
    · simp
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]

/-- The unsigned Whitney numbers of the Boolean (free) matroid on an `n`-element ground
set are the binomial coefficients `C(n, i)`. -/
