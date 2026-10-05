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
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem digit_ofSum (B : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < B) (n k : ℕ) :
    digit (∑ i ∈ range n, c i * B ^ i) B k = if k < n then c k else 0 := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hc 0)
  rcases lt_or_ge k n with hkn | hkn
  · rw [if_pos hkn]
    obtain ⟨d, rfl⟩ : ∃ d, n = k + (d + 1) := ⟨n - k - 1, by omega⟩
    rw [Finset.sum_range_add]
    have h2 : ∑ i ∈ range (d + 1), c (k + i) * B ^ (k + i)
        = B ^ k * (c k + B * ∑ i ∈ range d, c (k + 1 + i) * B ^ i) := by
      rw [Finset.sum_range_succ']
      simp [pow_add, Finset.mul_sum, mul_add, mul_comm, mul_left_comm, mul_assoc,
        pow_succ, add_comm, add_left_comm]
    rw [h2, digit, Nat.add_mul_div_left _ _ (Nat.pow_pos hB),
      Nat.div_eq_of_lt (sum_lt_pow c hc k)]
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc k)]
  · rw [if_neg (by omega)]
    have : ∑ i ∈ range n, c i * B ^ i < B ^ k :=
      lt_of_lt_of_le (sum_lt_pow c hc n) (Nat.pow_le_pow_right hB hkn)
    simp [digit, Nat.div_eq_of_lt this]

/-- Binomial coefficients are the base-`u` digits of `(u+1)^n`, for `u` large. -/
