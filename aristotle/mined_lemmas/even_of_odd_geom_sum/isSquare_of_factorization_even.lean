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

set_option grind.warning false


lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [← Finsupp.prod_mul]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

